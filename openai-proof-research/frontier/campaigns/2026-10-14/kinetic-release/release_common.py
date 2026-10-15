"""Shared local-release integrity checks. Copyright 2026 Myeongjin Kang; MIT."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import re
import stat
import subprocess
import sys
import tempfile

CAMPAIGN = 'frontier/campaigns/2026-10-14'
RELEASE = CAMPAIGN + '/kinetic-release'
MANUSCRIPT = CAMPAIGN + '/kinetic-manuscript'
REVIEW = CAMPAIGN + '/kinetic-manuscript-review-r1'
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
    'main.tex': '969c35d11d8242c35117b77233d2612761ac56bc231f7365acd2172ad6f08d29',
    'output/pdf/main.pdf': 'c7f2c4533c58d15157445b4b19044c2c1b324ce7972ea106ea158e4601412565',
    'outputs.json': 'cac9c988d0b4c839d47353a0ef54d1becf751b9fac89ea4978baf9b701329f66',
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

def check_record(root, row):
    if not isinstance(row, dict) or set(row) != {'path', 'sha256', 'bytes'}:
        raise ValueError('Expected exact path/hash/length record')
    if not isinstance(row['sha256'], str) or not re.fullmatch('[0-9a-f]{64}', row['sha256']):
        raise ValueError('Malformed SHA256')
    if type(row['bytes']) is not int or row['bytes'] < 0:
        raise ValueError('Malformed byte length')
    data = read_regular(root, row['path'])
    if sha(data) != row['sha256'] or len(data) != row['bytes']:
        raise ValueError(f'Frozen input mismatch: {row["path"]}')
    return data

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
    """Authenticate parent-configured disposition; never infer a verdict from PASS text."""
    if gate.get('schema') != 'kinetic-release-gate-v1':
        raise ValueError('Unknown gate schema')
    if gate.get('bound_manuscript') != bindings:
        raise ValueError('Gate does not bind the frozen manuscript hashes')
    if gate.get('state') == 'pending':
        if require_integrated:
            raise ValueError('Manuscript gate pending: no release archive may be created')
        return {}
    if gate.get('state') != 'integrated':
        raise ValueError('Unrecognized gate state')
    if (not isinstance(trusted_parent_sha256, str)
            or not re.fullmatch('[0-9a-f]{64}', trusted_parent_sha256)):
        raise ValueError('Supply the independently trusted parent disposition SHA256')
    selected = {}
    for key in ['review', 'review_manifest', 'reviewer_record', 'parent_disposition']:
        row = gate.get(key)
        if not isinstance(row, dict):
            raise ValueError(f'Missing configured gate record: {key}')
        selected[row['path']] = check_record(root, row)
    review = gate['review']; manifest = gate['review_manifest']; parent = gate['parent_disposition']
    if review['path'] != REVIEW+'/review.md' or manifest['path'] != REVIEW+'/outputs.json':
        raise ValueError('Unexpected manuscript-review paths')
    if (not parent['path'].startswith(PARENT+'/') or 'manuscript' not in Path(parent['path']).name
            or not parent['path'].endswith('.json')):
        raise ValueError('Parent disposition must be an actual manuscript integration record')
    if parent['sha256'] != trusted_parent_sha256:
        raise ValueError('Parent disposition differs from independently trusted hash')
    # Hashes authenticate bytes against a caller-supplied trust anchor. Neither
    # a PASS substring nor a gate author's assertion can substitute for it.
    disposition = json.loads(selected[parent['path']])
    if disposition.get('full_original_scope') is not True:
        raise ValueError('Parent must explicitly affirm the full original scope')
    required = {'schema': 'kinetic-manuscript-parent-disposition-v1',
                'authority': 'parent integration', 'manuscript_verdict': 'PASS',
                'full_original_scope': True, 'bound_manuscript': bindings,
                'review': review, 'review_manifest': manifest,
                'reviewer_record': gate['reviewer_record'], 'reviewer': gate.get('reviewer')}
    if any(disposition.get(k) != v for k, v in required.items()):
        raise ValueError('Parent disposition does not affirm the exact full-scope review and freeze')
    reviewer = gate.get('reviewer')
    if (not isinstance(reviewer, dict) or set(reviewer) != {'provider', 'model', 'task_id'}
            or any(not isinstance(v, str) or not v.strip() for v in reviewer.values())):
        raise ValueError('Actual reviewer provider/model/task identity required')
    rows = json.loads(selected[manifest['path']])
    rows = rows if isinstance(rows, list) else rows['files']
    indexed = {}
    for row in rows:
        name = row['path']
        safe_name(name)
        if not name.startswith(REVIEW+'/'):
            name = REVIEW+'/'+name
        safe_name(name)
        if not name.startswith(REVIEW+'/') or name in indexed:
            raise ValueError('Malformed review manifest membership')
        indexed[name] = {'path':name, 'sha256':row['sha256'], 'bytes':row['bytes']}
    for row in [review, gate['reviewer_record'], *gate.get('review_artifacts', [])]:
        name = row['path']
        if name not in indexed or row != indexed[name]:
            raise ValueError(f'Gate artifact not authenticated by review manifest: {name}')
        if excluded_payload(name):
            raise ValueError(f'Excluded gate payload: {name}')
        selected[name] = check_record(root, row)
    return selected


def read_json(root, name):
    return json.loads(read_regular(root, name))


def check_freeze(root):
    for name, expected in FROZEN_HASHES.items():
        if sha(read_regular(root, MANUSCRIPT+'/'+name)) != expected:
            raise ValueError('Manuscript freeze changed: '+name)
    rows = read_json(root, MANUSCRIPT+'/outputs.json')['files']
    if len(rows) != 46:
        raise ValueError('Expected 46 frozen manuscript outputs')
    for row in rows:
        check_record(root, {**row, 'path':MANUSCRIPT+'/'+row['path']})


def run_finite_checks(root):
    """Run isolated copies, including the slower mixed exact/numerical controls."""
    jobs = [
        (MANUSCRIPT+'/checks/repair_checks.py', 'file', 14),
        (MANUSCRIPT+'/checks/editorial_checks.py', 'file', 8),
        (MANUSCRIPT+'/checks/adversarial_checks.py', 'file', None),
        (CAMPAIGN+'/kinetic-proof-r2/checks/independent_controls.py', 'stdout', None),
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
