"""Shared local-release integrity checks. Copyright 2026 Myeongjin Kang; MIT."""
from pathlib import Path, PurePosixPath
import difflib
import hashlib
import json
import re
import stat
import subprocess
import sys
import tempfile

CAMPAIGN = 'frontier/campaigns/2026-10-14'
RELEASE = CAMPAIGN + '/kinetic-release-v2'
MANUSCRIPT = CAMPAIGN + '/kinetic-manuscript-consolidation'
ORIGINAL = CAMPAIGN + '/kinetic-manuscript'
ORIGINAL_REVIEW = CAMPAIGN + '/kinetic-manuscript-review-r1'
REVIEW = CAMPAIGN + '/kinetic-manuscript-review-r2'
PARENT = CAMPAIGN + '/kinetic-parent'
SCOPE = ('Actual unsmoothed deterministic grand-canonical hard spheres on R3_x x R3_v; '
         'excluded-product law including N=0, mu=epsilon^-2; exactly H ass:kinetic on '
         'the entire supplied regular Boltzmann interval; exact microscopic centering; '
         'every finite real C_c-infinity test vector; J1 convergence and C-tightness '
         'to the continuous Gaussian process. No uniform-topology weak-law assertion.')
FORMAL_SCOPE = ('Nine algebraic support declarations only: elastic-pair momentum and '
                'unit-normal squared-norm energy; four affine shift identities; '
                'finite all-line energy under pair replacement and simultaneous '
                'elastic update; rational exponents. No entering-root covariance, '
                'chronology Q, determinant/Jacobian, history existence, analytic '
                'estimate, tightness or path theorem is formalized.')
FROZEN_HASHES = {
    'main.tex': 'f2548882cf47aa4259c68b43ea38d755c395b47008300783856788ab5ef6fd38',
    'output/pdf/main.pdf': '08a092590559fa81c1d2c759e06efb9a03b1e7b6ede1d708ace731cc0f2028dc',
    'outputs.json': 'a299015528841be2324fc210ae59c3c48028c4c7448bcd8762a3e5502dee1536',
    'inputs.json': '66e05660c2f9636989f22ab7587fdc05dab27af73d1707821bc910f43fd0cf87',
}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def safe_name(name):
    if (not isinstance(name, str) or not name or '\\' in name or ':' in name
            or any(ord(c) < 32 for c in name)):
        raise ValueError(f'Unsafe project path: {name!r}')
    p = PurePosixPath(name)
    if p.is_absolute() or '..' in p.parts or p.as_posix() != name or name == '.':
        raise ValueError(f'Unsafe project path: {name!r}')
    return p

def read_regular(root, name):
    root = Path(root)
    if root.absolute() != root.resolve():
        raise ValueError('Symlink root is not allowed')
    relative = safe_name(name)
    target = root.joinpath(*relative.parts)
    current = root
    for part in relative.parts:
        current = current/part
        if current.is_symlink():
            raise ValueError(f'Symlink is not a release input: {name}')
    if not target.is_file() or not stat.S_ISREG(target.stat().st_mode):
        raise ValueError(f'Not a regular file: {name}')
    if not target.resolve().is_relative_to(root.resolve()):
        raise ValueError(f'Path escapes root: {name}')
    return target.read_bytes()

def record(name, data):
    safe_name(name)
    return {'path': name, 'sha256': sha(data), 'bytes': len(data)}

def validate_record(row):
    if not isinstance(row, dict) or set(row) != {'path', 'sha256', 'bytes'}:
        raise ValueError('Expected exact path/hash/length record')
    safe_name(row['path'])
    if not isinstance(row['sha256'], str) or not re.fullmatch('[0-9a-f]{64}', row['sha256']):
        raise ValueError('Malformed SHA256')
    if type(row['bytes']) is not int or row['bytes'] < 0:
        raise ValueError('Malformed byte length')
    return row


def check_record(root, row):
    validate_record(row)
    data = read_regular(root, row['path'])
    if sha(data) != row['sha256'] or len(data) != row['bytes']:
        raise ValueError(f'Frozen input mismatch: {row["path"]}')
    return data


def decode_json(raw):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError('Duplicate JSON key: '+key)
            result[key] = value
        return result
    return json.loads(raw, object_pairs_hook=unique)


def manifest_records(data, base=None):
    """Accept an explicit list, files object, or outputs object, never guess.

    Relative paths resolve inside base; project-relative paths must already
    start with base. Validate all rows, including unselected historical rows.
    """
    if isinstance(data, dict):
        keys = set(data) & {'files', 'outputs'}
        if len(keys) != 1:
            raise ValueError('Manifest requires exactly one of files or outputs')
        data = data[next(iter(keys))]
    if not isinstance(data, list):
        raise ValueError('Manifest rows must be a list')
    indexed = {}
    if base is not None:
        safe_name(base)
    for row in data:
        validate_record(row)
        name = row['path']
        if base is not None and not name.startswith(base+'/'):
            if name.startswith(('frontier/', 'sources/')):
                raise ValueError('Manifest path outside its artifact directory: '+name)
            name = base+'/'+name
        safe_name(name)
        if name in indexed:
            raise ValueError('Duplicate normalized manifest path: '+name)
        indexed[name] = {**row, 'path':name}
    return indexed

def excluded_payload(name):
    p = safe_name(name)
    return (any(part in {'.lake', '__pycache__', '.git', 'fetched-H', 'corpus'} for part in p.parts)
            or p.suffix in {'.olean', '.ilean', '.o', '.a', '.so', '.pyc'}
            or 'kinetic-window-discovery/fetched-' in name)

def discover_root(here):
    for ancestor in [here, *here.parents]:
        if ((ancestor/'BUNDLE-MANIFEST.json').is_file()
            or ((ancestor/'AGENTS.md').is_file() and (ancestor/'sources/upstream.json').is_file())):
            return ancestor
    raise ValueError('Cannot discover project/package root; provide it explicitly.')

def validate_gate(root, gate, bindings, require_integrated, trusted_parent_sha256=None):
    """Parent assertion and byte bindings; never parse verdict words from prose."""
    if not isinstance(gate, dict) or gate.get('schema') != 'kinetic-release-gate-v2':
        raise ValueError('Unknown gate schema')
    if gate.get('bound_manuscript') != bindings or gate.get('manuscript_path') != MANUSCRIPT:
        raise ValueError('Gate does not bind the corrected manuscript path and hashes')
    if gate.get('state') == 'pending':
        if require_integrated:
            raise ValueError('Manuscript gate pending: no release archive may be created')
        if (any(gate.get(k) is not None for k in
                ['review', 'review_manifest', 'reviewer_record', 'reviewer', 'reviewer_identity_basis', 'parent_disposition'])
                or gate.get('review_artifacts') != []):
            raise ValueError('Pending gate cannot contain anticipated review records')
        return {}
    if gate.get('state') != 'integrated':
        raise ValueError('Unrecognized gate state')
    if (not isinstance(trusted_parent_sha256, str)
            or not re.fullmatch('[0-9a-f]{64}', trusted_parent_sha256)):
        raise ValueError('Supply the independently trusted parent disposition SHA256')
    reviewer = gate.get('reviewer')
    if (not isinstance(reviewer, dict) or set(reviewer) != {'provider', 'model', 'task_id'}
            or any(not isinstance(v, str) or not v.strip() for v in reviewer.values())):
        raise ValueError('Actual reviewer provider/model/task identity required')
    identity_basis = gate.get('reviewer_identity_basis')
    if not isinstance(identity_basis, str) or not identity_basis.strip():
        raise ValueError('Parent must explain the actual reviewer identity/provenance binding')
    selected = {}
    for key in ['review', 'review_manifest', 'reviewer_record', 'parent_disposition']:
        row = validate_record(gate.get(key))
        if excluded_payload(row['path']):
            raise ValueError('Excluded gate payload: '+row['path'])
        selected[row['path']] = check_record(root, row)
    review = gate['review']; manifest = gate['review_manifest']; parent = gate['parent_disposition']
    if review['path'] != REVIEW+'/review.md' or manifest['path'] != REVIEW+'/outputs.json':
        raise ValueError('Unexpected corrected-edition manuscript-review paths')
    if (not parent['path'].startswith(PARENT+'/') or 'manuscript' not in Path(parent['path']).name
            or not parent['path'].endswith('.json')):
        raise ValueError('Parent disposition must be an actual manuscript integration record')
    if parent['sha256'] != trusted_parent_sha256:
        raise ValueError('Parent disposition differs from independently trusted hash')
    required = {'schema': 'kinetic-manuscript-parent-disposition-v2',
                'authority': 'parent integration', 'manuscript_verdict': 'PASS',
                'full_original_scope': True, 'manuscript_path': MANUSCRIPT,
                'bound_manuscript': bindings, 'review': review, 'review_manifest': manifest,
                'reviewer_record': gate['reviewer_record'], 'reviewer': reviewer,
                'reviewer_identity_basis': identity_basis}
    disposition = decode_json(selected[parent['path']])
    if not isinstance(disposition, dict) or any(disposition.get(k) != v for k, v in required.items()):
        raise ValueError('Parent disposition does not affirm the exact full-scope review and freeze')
    # bool is a subclass of int; require a JSON boolean, not numeric 1.
    if disposition.get('full_original_scope') is not True:
        raise ValueError('Parent must explicitly affirm the full original scope')
    indexed = manifest_records(decode_json(selected[manifest['path']]), REVIEW)
    if manifest['path'] in indexed:
        raise ValueError('Review manifest must not hash itself')
    artifacts = gate.get('review_artifacts')
    if not isinstance(artifacts, list):
        raise ValueError('review_artifacts must be an explicit list')
    artifact_names = set()
    for row in artifacts:
        validate_record(row)
        if row['path'] in artifact_names or row['path'] in {review['path'], gate['reviewer_record']['path']}:
            raise ValueError('Duplicate configured review artifact')
        artifact_names.add(row['path'])
    # reviewer_record may intentionally equal review: identity can be embedded
    # in a real manifest member, with the parent attesting to its provenance.
    for row in [review, gate['reviewer_record'], *artifacts]:
        name = row['path']
        if name not in indexed or row != indexed[name]:
            raise ValueError('Gate artifact not authenticated by review manifest: '+name)
        if excluded_payload(name):
            raise ValueError('Excluded gate payload: '+name)
        selected[name] = check_record(root, row)
    return selected


def read_json(root, name):
    return decode_json(read_regular(root, name))


def check_freeze(root):
    for name, expected in FROZEN_HASHES.items():
        if sha(read_regular(root, MANUSCRIPT+'/'+name)) != expected:
            raise ValueError('Manuscript freeze changed: '+name)
    rows = manifest_records(read_json(root, MANUSCRIPT+'/outputs.json'), MANUSCRIPT)
    if len(rows) != 57 or MANUSCRIPT+'/outputs.json' in rows:
        raise ValueError('Expected 57 non-self-referential frozen manuscript outputs')
    for row in rows.values():
        check_record(root, row)
    if len(manifest_records(read_json(root, MANUSCRIPT+'/inputs.json'))) != 107:
        raise ValueError('Expected 107 historical input records')
    original = read_regular(root, ORIGINAL+'/main.tex').decode().splitlines(keepends=True)
    corrected = read_regular(root, MANUSCRIPT+'/main.tex').decode().splitlines(keepends=True)
    diff = ''.join(difflib.unified_diff(original, corrected,
        fromfile='kinetic-manuscript/main.tex', tofile='kinetic-manuscript-consolidation/main.tex'))
    if diff.encode() != read_regular(root, MANUSCRIPT+'/original-to-consolidated.diff'):
        raise ValueError('Exact original-to-corrected TeX diff mismatch')
    # The actual original review authenticates only the original edition.
    pins = {'review.md':'be96cc4ca94c3e7e1d46b908768b29008ae886a4b84309cc1d136a69115f54e1',
            'outputs.json':'82ea15f91395b9ccd205c6a767323ee4834da83411e944138be16cd74b59fb1b'}
    for name, expected in pins.items():
        if sha(read_regular(root, ORIGINAL_REVIEW+'/'+name)) != expected:
            raise ValueError('Historical manuscript review changed: '+name)
    history = read_json(root, ORIGINAL_REVIEW+'/outputs.json')
    rows = manifest_records(history, ORIGINAL_REVIEW)
    if len(rows) != 4:
        raise ValueError('Expected four historical review outputs')
    for row in rows.values():
        check_record(root, row)
    for name, key in [('main.tex','reviewed_main_tex_sha256'),
                      ('output/pdf/main.pdf','reviewed_pdf_sha256'),
                      ('outputs.json','reviewed_outputs_json_sha256')]:
        if sha(read_regular(root, ORIGINAL+'/'+name)) != history[key]:
            raise ValueError('Original review does not bind original edition: '+name)


def run_finite_checks(root):
    """Run isolated copies, including the slower mixed exact/numerical controls."""
    jobs = [
        (MANUSCRIPT+'/checks/repair_checks.py', 'file', 14),
        (MANUSCRIPT+'/checks/editorial_checks.py', 'file', 8),
        (MANUSCRIPT+'/checks/adversarial_checks.py', 'file', None),
        (CAMPAIGN+'/kinetic-proof-r2/checks/independent_controls.py', 'stdout', None),
        (ORIGINAL_REVIEW+'/independent_controls.py', 'file', 12),
    ]
    results = []
    with tempfile.TemporaryDirectory(prefix='kinetic-finite-') as directory:
        temp = Path(directory)
        for i, (name, mode, count) in enumerate(jobs):
            script = temp / str(i) / Path(name).name
            script.parent.mkdir()
            script.write_bytes(read_regular(root, name))
            expected = read_regular(root, str(PurePosixPath(name).with_suffix('.json')))
            run = subprocess.run([sys.executable, '-I', str(script)], cwd=script.parent,
                                 capture_output=True, timeout=300, check=True)
            actual = script.with_suffix('.json').read_bytes() if mode == 'file' else run.stdout
            if actual != expected:
                raise ValueError('Finite-check receipt differs: '+name)
            parsed = json.loads(actual)
            if count is not None and (parsed.get('count') != count
                                      or not all(v is True for v in parsed['checks'].values())):
                raise ValueError('Unexpected named check count: '+name)
            results.append({'script':name, 'receipt_sha256':sha(actual),
                            'bytes_identical':True, 'named_count':count})
    return results
