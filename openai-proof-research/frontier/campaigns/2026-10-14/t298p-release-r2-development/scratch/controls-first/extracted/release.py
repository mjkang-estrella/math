#!/usr/bin/env python3
"""T298P portable local preparation, gated assembly, identity and replay.
Copyright 2026 Myeongjin Kang. MIT. No upload or acceptance operation.
"""
import argparse
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import zipfile

HERE = Path(__file__).absolute().parent
MANUSCRIPT = 'afc2c2ad6ecd45ef9958092c343e99b9d2804cb8f771a3d54cccae3e426393dc'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
NEGATIVE = ['denominator-k2', 'no-column-gram', 'no-endpoint', 'reversed-gap', 'weak-error']
TEMPLATES = {'README.md': 'README.md', 'RIGHTS.md': 'RIGHTS.md',
             'PROVENANCE.md': 'PROVENANCE.md', 'NEGATIVE-FIXTURES.md': 'formal/reviewer/NEGATIVE-FIXTURES.md'}
MAX_FILE = 16 * 1024 * 1024
MAX_TOTAL = 128 * 1024 * 1024


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def record(raw):
    return {'bytes': len(raw), 'sha256': sha(raw)}


def encoded(obj):
    return (json.dumps(obj, indent=2, sort_keys=True) + '\n').encode()


def unique_pairs(items):
    out = {}
    for k, v in items:
        need(k not in out, 'duplicate JSON key')
        out[k] = v
    return out


def parse(raw):
    return json.loads(raw, object_pairs_hook=unique_pairs)


def anchor(value):
    need(isinstance(value, str) and re.fullmatch('[0-9a-f]{64}', value), 'malformed external anchor')


def safe(name):
    need(isinstance(name, str) and name, 'empty/non-string path')
    p = PurePosixPath(name)
    need(not p.is_absolute() and name == p.as_posix() and name != '.'
         and '..' not in p.parts and '\\' not in name and ':' not in name and '\x00' not in name,
         'unsafe relative path')
    need(len(name) <= 240 and all(re.fullmatch(r'[A-Za-z0-9_.-]+', x) and not x.endswith('.') for x in p.parts), 'nonportable path')
    need(not any(x.split('.')[0].upper() in {'CON','PRN','AUX','NUL', *['COM'+str(i) for i in range(1,10)], *['LPT'+str(i) for i in range(1,10)]} for x in p.parts), 'reserved portable path')
    return p


def public(name):
    p = safe(name)
    need(not any(x in {'private', 'tmp', 'scratch', '.lake', '.git', '__pycache__', 'node_modules', '.env'}
                 for x in p.parts), 'private/cache/transient payload forbidden')
    need(not name.lower().endswith('.pdf') or name == 'paper/output/pdf/main.pdf', 'only original manuscript PDF may be redistributed')
    need(not name.endswith(('.olean', '.ilean', '.pyc', '.so', '.o', '.key')), 'compiled/secret payload forbidden')


def absolute(path):
    path = Path(path).absolute()
    need('..' not in path.parts, 'non-normalized absolute path')
    return path


def ancestry(path):
    for part in reversed(path.parents):
        need(stat.S_ISDIR(part.lstat().st_mode), 'linked/non-directory ancestry')


def read(root, name):
    p = absolute(root).joinpath(*safe(name).parts)
    ancestry(p)
    st = p.lstat()
    need(stat.S_ISREG(st.st_mode) and st.st_nlink == 1, 'nonregular or linked input: ' + name)
    need(st.st_size <= MAX_FILE, 'file size budget')
    return p.read_bytes()


def inventory(root, exclude=()):
    root = absolute(root)
    ancestry(root)
    need(stat.S_ISDIR(root.lstat().st_mode), 'linked/non-directory root')
    files, dirs = {}, set()
    def walk(base):
        for entry in sorted(os.scandir(base), key=lambda e: e.name):
            p = Path(entry.path)
            rel = p.relative_to(root).as_posix()
            if base == root and entry.name in exclude:
                continue
            st = p.lstat()
            if stat.S_ISDIR(st.st_mode):
                dirs.add(rel)
                walk(p)
            else:
                files[rel] = read(root, rel)
    walk(root)
    need(sum(map(len, files.values())) <= MAX_TOTAL, 'total size budget')
    return files, sorted(dirs)


def dirs_for(names):
    return sorted({p.as_posix() for name in names for p in safe(name).parents if p.as_posix() != '.'})


def member_hash(mf, name):
    fs = mf['files']
    if isinstance(fs, list):
        need(len({x['path'] for x in fs}) == len(fs), 'duplicate original manifest member')
        fs = {x['path']: x for x in fs}
    rec = fs.get(name)
    need(rec is not None, 'file missing from original manifest: ' + name)
    return rec if isinstance(rec, str) else rec['sha256']


def manifest(payload, kind, gate=None):
    need('MANIFEST.json' not in payload, 'manifest cannot self-list')
    return encoded({'schema': 't298p-bundle-v1', 'kind': kind, 'accepted': False,
                    'published': False, 'count_change': 0, 'full_theorem_formalized': False,
                    'source_pin': PIN, 'manuscript_anchor': MANUSCRIPT, 'gate': gate,
                    'directories': dirs_for(payload),
                    'files': {n: record(b) for n, b in sorted(payload.items())}})


def pointer(obj, path):
    need(isinstance(path, str) and (path == '' or path.startswith('/')), 'invalid JSON pointer')
    for token in path.split('/')[1:] if path else []:
        token = token.replace('~1', '/').replace('~0', '~')
        obj = obj[int(token)] if isinstance(obj, list) else obj[token]
    return obj


def review_gate(get, review_anchor, policy_raw, policy_anchor):
    """Layout is supplied only after the actual sealed reviewer schema is known."""
    anchor(review_anchor); anchor(policy_anchor)
    need(sha(policy_raw) == policy_anchor, 'external review-policy anchor mismatch')
    policy = parse(policy_raw)
    need(policy['schema'] == 't298p-review-layout-v1', 'review layout policy schema')
    need(policy['review_anchor'] == review_anchor and policy['manuscript_anchor'] == MANUSCRIPT,
         'review policy binding')
    raw = get('MANIFEST.json')
    need(sha(raw) == review_anchor, 'external manuscript-review anchor mismatch')
    rm = parse(raw)
    include = policy['include']
    need(isinstance(include, list) and len(include) == len(set(include)), 'review include allowlist')
    need(policy['report'] in include, 'human review report must be included')
    for name in include:
        public(name)
        if name != 'MANIFEST.json':
            need(sha(get(name)) == member_hash(rm, name), 'selected manuscript-review file mismatch')
    def value(spec):
        name = spec['file']; public(name)
        need(name == 'MANIFEST.json' or name in include, 'unselected gate evidence')
        if name != 'MANIFEST.json':
            need(sha(get(name)) == member_hash(rm, name), 'unbound gate evidence')
        return pointer(parse(get(name)), spec['pointer'])
    v = value(policy['verdict'])
    expected = policy['verdict']['pass_value']
    need(isinstance(expected, str) and re.fullmatch(r'PASS(?:_[A-Z0-9]+)*', expected),
         'policy must name an explicit PASS verdict')
    need(type(v) is str and v == expected, 'actual manuscript review did not PASS')
    findings = value(policy['required_findings'])
    need(type(findings) is list and findings == [],
         'actual manuscript review has required findings or ambiguous count')
    binding = value(policy['manuscript_binding'])
    need(type(binding) is str and binding == MANUSCRIPT, 'review does not bind the frozen manuscript')
    return policy


def validate_provenance(payload):
    selection = parse(payload['selection.json'])
    need(selection['schema'] == 't298p-selection-v1' and selection['source_pin'] == PIN,
         'selection/source pin mismatch')
    need(selection['anchors']['t298p-manuscript-r2'] == MANUSCRIPT, 'manuscript selection anchor')
    manifests = {}
    for package, expected in selection['anchors'].items():
        safe(package); anchor(expected)
        raw = payload['attestations/' + package + '-MANIFEST.json']
        need(sha(raw) == expected, 'selected original manifest anchor')
        manifests[package] = parse(raw)
    destinations = set()
    for row in selection['files']:
        name = row['destination']; public(name)
        need(name not in destinations, 'duplicate selection destination'); destinations.add(name)
        need(record(payload[name]) == {'bytes': row['bytes'], 'sha256': row['sha256']},
             'selected payload bytes mismatch')
        if row['source'] != 'MANIFEST.json':
            need(sha(payload[name]) == member_hash(manifests[row['packet']], row['source']),
                 'selected payload not bound by frozen original')
    fv = parse(payload['formal/reviewer/verdict.json'])
    need(fv['verdict'] == 'PASS' and fv['required_findings'] == []
         and fv['full_theorem_formalized'] is False, 'scoped formal review mismatch')
    audit = parse(payload['formal/reviewer/reference/receipt.json'])
    need(len(audit['kernel_dependencies']) == 18 and len(audit['expected_rejections']) == 5,
         'formal review reference coverage')
    need([r['step'] for r in audit['expected_rejections']] == NEGATIVE,
         'wrong negative fixture set')
    for row in audit['expected_rejections']:
        label = row['step']
        need(row['exit_code'] != 0, 'negative fixture advertised as successful')
        need(sha(payload['formal/reviewer/negative-fixtures/' + label + '.log']) == row['output_sha256'],
             'negative fixture rejection log mismatch')
    return selection


def validate_bytes(payload, expected, actual_dirs=None):
    anchor(expected)
    need('MANIFEST.json' in payload and sha(payload['MANIFEST.json']) == expected,
         'external bundle anchor mismatch')
    mf = parse(payload['MANIFEST.json'])
    need(mf['schema'] == 't298p-bundle-v1', 'bundle schema')
    need(len({n.casefold() for n in payload}) == len(payload), 'case-insensitive path collision')
    need(set(payload) == set(mf['files']) | {'MANIFEST.json'}, 'exact file membership')
    need(mf['directories'] == dirs_for(mf['files']), 'manifest directory list')
    if actual_dirs is not None:
        need(actual_dirs == mf['directories'], 'exact directory membership')
    for name, rec in mf['files'].items():
        public(name)
        need(record(payload[name]) == rec, 'payload size/hash mismatch: ' + name)
    need(mf['accepted'] is False and mf['published'] is False and type(mf['count_change']) is int
         and mf['count_change'] == 0 and mf['full_theorem_formalized'] is False,
         'unsupported acceptance/formal claim')
    need(mf['source_pin'] == PIN and mf['manuscript_anchor'] == MANUSCRIPT, 'fixed theorem binding')
    validate_provenance(payload)
    need(sha(payload['paper/main.tex']) == '499c2a2e6d14d70f47f39acde47c6404ce2101a91985998e363f9e1fe229b397', 'active manuscript source binding')
    need(sha(payload['paper/output/pdf/main.pdf']) == 'd460d6c916fd83b2f5a3a1554664ac335d6777d97a4787dec360cfd57171b740', 'active manuscript PDF binding')
    if mf['kind'] == 'PREPARATION_ONLY':
        need(mf['gate'] is None and not any(n.startswith('reviews/manuscript/') for n in payload),
             'preparation cannot carry invented manuscript gate')
    else:
        need(mf['kind'] == 'REVIEWABLE_LOCAL_RELEASE', 'unsupported bundle kind')
        gate = mf['gate']
        review_gate(lambda n: payload['reviews/manuscript/original/' + n], gate['review_anchor'],
                    payload['reviews/manuscript/layout-policy.json'], gate['policy_anchor'])
    return mf


def verify(root, expected):
    files, dirs = inventory(root)
    return validate_bytes(files, expected, dirs), files


def new_output(path, inputs):
    path = absolute(path); ancestry(path)
    need(not path.exists() and not path.is_symlink(), 'output must be fresh')
    for source in inputs:
        source = absolute(source)
        need(not path.is_relative_to(source) and not source.is_relative_to(path), 'output overlaps input')
    return path


def write_tree(root, payload):
    root.mkdir(parents=False, exist_ok=False)
    for name, data in sorted(payload.items()):
        public(name)
        path = root.joinpath(*safe(name).parts)
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open('xb') as stream:
            stream.write(data)
        path.chmod(0o644)


def implementation(expected):
    files, dirs = inventory(HERE, exclude=('scratch',))
    anchor(expected)
    raw = files.pop('IMPLEMENTATION-MANIFEST.json')
    need(sha(raw) == expected, 'external implementation anchor mismatch')
    mf = parse(raw)
    need(mf['schema'] == 't298p-release-implementation-v1', 'implementation schema')
    need(set(files) == set(mf['files']), 'implementation exact file membership')
    need(dirs == mf['directories'], 'implementation exact directory membership')
    for n, b in files.items():
        need(record(b) == mf['files'][n], 'implementation file mismatch: ' + n)


def prepare(a):
    implementation(a.implementation_anchor)
    root = absolute(a.repo) / 'frontier/campaigns/2026-10-14'
    selection_raw = read(HERE, 'selection.json'); selection = parse(selection_raw)
    payload = {'selection.json': selection_raw, 'release.py': read(HERE, 'release.py')}
    manifests = {}
    for pkg, expected in selection['anchors'].items():
        raw = read(root / pkg, 'MANIFEST.json')
        need(sha(raw) == expected, 'original external anchor: ' + pkg)
        manifests[pkg] = parse(raw)
    for row in selection['files']:
        safe(row['source']); public(row['destination'])
        raw = read(root / row['packet'], row['source'])
        need(record(raw) == {'bytes': row['bytes'], 'sha256': row['sha256']}, 'selected input mismatch')
        if row['source'] != 'MANIFEST.json':
            need(sha(raw) == member_hash(manifests[row['packet']], row['source']), 'unbound selected input')
        need(row['destination'] not in payload, 'selection collision')
        payload[row['destination']] = raw
    for source, target in TEMPLATES.items():
        payload[target] = read(HERE / 'templates', source)
    receipts = parse(payload['proof/original/source-receipts.json'])
    dependencies = {'upstream_pin': PIN, 'redistributed_source_bodies': False,
                    'canonical_sources': [{**r, 'immutable_url': 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + r['path']}
                                          for r in receipts['files']],
                    'external_primary_papers': parse(payload['proof/original/primary-receipts.json'])}
    payload['DEPENDENCIES.json'] = encoded(dependencies)
    payload['MANIFEST.json'] = manifest(payload, 'PREPARATION_ONLY')
    validate_bytes(payload, sha(payload['MANIFEST.json']))
    # A development child is permitted; all original input packets remain disjoint.
    output = new_output(a.output, [root / p for p in selection['anchors']])
    write_tree(output, payload)
    print(json.dumps({'kind': 'PREPARATION_ONLY', 'manifest_sha256': sha(payload['MANIFEST.json']),
                      'files': len(payload)-1, 'manuscript_gate': 'not supplied; archive assembly disabled'}))


def stable_zip(path, payload):
    with zipfile.ZipFile(path, 'x', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for name, data in sorted(payload.items()):
            public(name)
            info = zipfile.ZipInfo(name, (2026, 10, 18, 0, 0, 0))
            info.create_system = 3; info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            z.writestr(info, data, compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)


def zip_payload(path, expected_archive):
    anchor(expected_archive)
    raw = read(absolute(path).parent, absolute(path).name)
    need(sha(raw) == expected_archive, 'external archive hash mismatch')
    with zipfile.ZipFile(io.BytesIO(raw)) as z:
        infos = z.infolist(); names = [i.filename for i in infos]
        need(names == sorted(set(names)) and not z.comment, 'archive order/duplicate/comment')
        need(sum(i.file_size for i in infos) <= MAX_TOTAL, 'archive total size budget')
        for i in infos:
            public(i.filename)
            need(not i.is_dir() and i.file_size <= MAX_FILE and i.create_system == 3
                 and i.external_attr == 0o100644 << 16 and i.internal_attr == 0
                 and i.date_time == (2026,10,18,0,0,0) and i.compress_type == zipfile.ZIP_DEFLATED
                 and not i.extra and not i.comment and i.flag_bits == 0,
                 'unsafe/noncanonical archive member')
        return {i.filename: z.read(i) for i in infos}


def archive_preparation(a):
    mf, payload = verify(a.prepared, a.preparation_anchor)
    need(mf['kind'] == 'PREPARATION_ONLY', 'only preparation permitted by this command')
    output = new_output(a.output, [a.prepared])
    stable_zip(output, payload)
    archive_hash = sha(output.read_bytes())
    validate_bytes(zip_payload(output, archive_hash), a.preparation_anchor)
    print(json.dumps({'kind':'PREPARATION_ONLY', 'archive_sha256':archive_hash, 'manifest_sha256':a.preparation_anchor, 'accepted':False}))


def assemble(a):
    _, payload = verify(a.prepared, a.preparation_anchor)
    need(parse(payload['MANIFEST.json'])['kind'] == 'PREPARATION_ONLY', 'assembly requires preparatory input')
    # No output or archive is created before all actual manuscript gate checks succeed.
    need(a.manuscript_review is not None and a.review_anchor and a.review_policy and a.policy_anchor,
         'actual sealed manuscript PASS and explicit authenticated layout policy required')
    review = absolute(a.manuscript_review)
    policy_raw = read(absolute(a.review_policy).parent, absolute(a.review_policy).name)
    pol = review_gate(lambda n: read(review, n), a.review_anchor, policy_raw, a.policy_anchor)
    payload.pop('MANIFEST.json')
    for name in sorted(set(pol['include']) | {'MANIFEST.json'}):
        payload['reviews/manuscript/original/' + name] = read(review, name)
    payload['reviews/manuscript/layout-policy.json'] = policy_raw
    gate = {'review_anchor': a.review_anchor, 'policy_anchor': a.policy_anchor}
    payload['MANIFEST.json'] = manifest(payload, 'REVIEWABLE_LOCAL_RELEASE', gate)
    expected = sha(payload['MANIFEST.json']); validate_bytes(payload, expected)
    output = new_output(a.output, [a.prepared, review, absolute(a.review_policy).parent])
    output.mkdir()
    write_tree(output / 'payload', payload)
    stable_zip(output / 't298p-release.zip', payload)
    archive_hash = sha((output / 't298p-release.zip').read_bytes())
    validate_bytes(zip_payload(output / 't298p-release.zip', archive_hash), expected)
    receipt = {'kind': 'REVIEWABLE_LOCAL_RELEASE', 'accepted': False, 'published': False,
               'count_change': 0, 'manifest_sha256': expected, 'archive_sha256': archive_hash,
               'gate': gate, 'full_theorem_formalized': False}
    (output / 'handoff.json').write_bytes(encoded(receipt))
    print(json.dumps(receipt))


def extract(a):
    payload = zip_payload(a.archive, a.archive_sha256)
    mf = validate_bytes(payload, a.anchor)
    output = new_output(a.output, [a.archive])
    with tempfile.TemporaryDirectory(prefix='.t298p-extract-', dir=output.parent) as td:
        temp = Path(td) / 'payload'; write_tree(temp, payload)
        verify(temp, a.anchor)
        temp.rename(output)
    print(json.dumps({'status': 'PASS_SAFE_EXTRACTION', 'kind': mf['kind'], 'manifest_sha256': a.anchor}))


def execute(command, log, cwd=None):
    run = subprocess.run(command, cwd=cwd, text=True, capture_output=True)
    log.write_text(run.stdout + run.stderr)
    need(run.returncode == 0, 'replay command failed; see ' + str(log))


def replay(a):
    mf, payload = verify(a.bundle, a.anchor)
    output = new_output(a.output, [a.bundle])
    mode = a.mode
    need(mode not in ('pdf','all') or a.tectonic is not None, 'explicit installed Tectonic required')
    need(mode not in ('author','reviewer','all') or (a.lean is not None and a.cache is not None),
         'explicit installed Lean and trusted pinned cache required')
    if a.tectonic:
        ref = parse(payload['paper/validation/build-receipt.json'])
        need(sha(read(absolute(a.tectonic).parent, absolute(a.tectonic).name)) == ref['tectonic_binary_sha256'],
             'Tectonic executable differs from recorded build')
    if a.lean:
        ref = parse(payload['formal/reviewer/reference/receipt.json'])
        need(sha(read(absolute(a.lean).parent, absolute(a.lean).name)) == ref['lean_binary_sha256'],
             'Lean executable differs from reviewed build')
    output.mkdir(); work = output / 'work'; work.mkdir()
    result = {'kind': mf['kind'], 'manifest_sha256': a.anchor, 'mode': mode,
              'full_theorem_formalized': False, 'accepted': False, 'checks': {}}
    try:
        if mode in ('pdf','all'):
            src = work / 'paper'
            write_tree(src, {n: payload['paper/'+n] for n in ['main.tex','build.py']})
            execute([sys.executable,'-I','-B',str(src/'build.py'),'--tectonic',str(absolute(a.tectonic)),
                     '--output',str(output/'pdf-build')],output/'pdf-command.log')
            need((output/'pdf-build/main.pdf').read_bytes() == payload['paper/output/pdf/main.pdf'],
                 'rebuilt PDF differs; compiler/TeX bundle trust boundary')
            result['checks']['pdf'] = {'byte_identical': True, 'sha256': sha(payload['paper/output/pdf/main.pdf'])}
        if mode in ('author','reviewer','all'):
            source_names = ['T298P.lean','Controls.lean','rebuild.py','lake-manifest.json','lakefile.toml','lean-toolchain']
            src = work / 'author'; write_tree(src, {n:payload['formal/author/'+n] for n in source_names})
        if mode in ('author','all'):
            execute([sys.executable,'-I','-B',str(src/'rebuild.py'),'--lean',str(absolute(a.lean)),
                     '--cache',str(absolute(a.cache)),'--output',str(output/'author-build')],output/'author-command.log')
            for name in ['support.log','controls.log','types-axioms.log','Checks.lean']:
                need((output/'author-build'/name).read_bytes() == payload['formal/author/reference/'+name],
                     'author reference differs: '+name)
            actual=parse((output/'author-build/receipt.json').read_bytes())
            ref=parse(payload['formal/author/reference/receipt.json'])
            for key in ['status','sources','kernel_dependencies','declarations','dependencies','lean_binary_sha256']:
                need(actual[key] == ref[key], 'author replay receipt differs: '+key)
            result['checks']['author']={'declarations':8,'reference_logs_identical':3,'types_and_axioms_identical':True}
        if mode in ('reviewer','all'):
            audit_src=work/'reviewer'
            rows={'audit.py':payload['formal/reviewer/audit.py'],'Independent.lean':payload['formal/reviewer/Independent.lean']}
            rows.update({'copied-author/'+n:payload['formal/author/'+n] for n in source_names})
            write_tree(audit_src,rows)
            execute([sys.executable,'-I','-B',str(audit_src/'audit.py'),'--lean',str(absolute(a.lean)),
                     '--cache',str(absolute(a.cache)),'--output',str(output/'reviewer-build')],output/'reviewer-command.log')
            for name in ['T298P.log','Controls.log','Independent.log','types-axioms.log','Checks.lean']:
                need((output/'reviewer-build'/name).read_bytes() == payload['formal/reviewer/reference/'+name],
                     'independent reference differs: '+name)
            for label in NEGATIVE:
                for ext in ['lean','log']:
                    need((output/'reviewer-build'/f'{label}.{ext}').read_bytes() ==
                         payload[f'formal/reviewer/negative-fixtures/{label}.{ext}'], 'negative fixture/reference differs')
            actual=parse((output/'reviewer-build/receipt.json').read_bytes())
            ref=parse(payload['formal/reviewer/reference/receipt.json'])
            for key in ['status','sources','kernel_dependencies','runs','expected_rejections','dependencies','lean_binary_sha256']:
                need(actual[key] == ref[key], 'independent replay receipt differs: '+key)
            need(len(actual['kernel_dependencies']) == 18, 'expected 18 type/axiom reports')
            need(all(r['exit_code'] != 0 for r in actual['expected_rejections']), 'negative fixtures must reject')
            result['checks']['reviewer']={'declarations':18,'reference_logs_identical':9,
                                        'expected_rejections':5,'negative_fixtures_are_not_theorems':True}
        # Recheck sealed inputs after every replay. Outputs are outside the bundle.
        verify(a.bundle,a.anchor)
        result['status']='PASS_SELECTED_REPLAY'
    except Exception as error:
        result.update(status='FAILED',error=str(error)); raise
    finally:
        (output/'replay-receipt.json').write_bytes(encoded(result))
    print(json.dumps(result))


def main():
    ap=argparse.ArgumentParser(description=__doc__); sub=ap.add_subparsers(dest='command',required=True)
    p=sub.add_parser('verify-implementation');p.add_argument('--implementation-anchor',required=True)
    p=sub.add_parser('prepare');p.add_argument('--repo',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--implementation-anchor',required=True)
    p=sub.add_parser('verify');p.add_argument('--bundle',type=Path,required=True);p.add_argument('--anchor',required=True)
    p=sub.add_parser('archive-preparation');p.add_argument('--prepared',type=Path,required=True);p.add_argument('--preparation-anchor',required=True);p.add_argument('--output',type=Path,required=True)
    p=sub.add_parser('assemble');p.add_argument('--prepared',type=Path,required=True);p.add_argument('--preparation-anchor',required=True);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--manuscript-review',type=Path);p.add_argument('--review-anchor');p.add_argument('--review-policy',type=Path);p.add_argument('--policy-anchor')
    p=sub.add_parser('extract');p.add_argument('--archive',type=Path,required=True);p.add_argument('--archive-sha256',required=True);p.add_argument('--anchor',required=True);p.add_argument('--output',type=Path,required=True)
    p=sub.add_parser('replay');p.add_argument('--bundle',type=Path,required=True);p.add_argument('--anchor',required=True);p.add_argument('--mode',choices=['identity','pdf','author','reviewer','all'],required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--tectonic',type=Path);p.add_argument('--lean',type=Path);p.add_argument('--cache',type=Path)
    a=ap.parse_args()
    if a.command=='verify-implementation':
        implementation(a.implementation_anchor)
        print(json.dumps({'status':'PASS_IMPLEMENTATION_IDENTITY_ONLY'}))
    elif a.command=='verify':
        mf,_=verify(a.bundle,a.anchor)
        print(json.dumps({'status':'PASS_IDENTITY_ONLY','kind':mf['kind'],'payload_files':len(mf['files']),
                          'full_theorem_formalized':False,'accepted':False}))
    else:
        globals()[a.command.replace('-', '_')](a)

if __name__=='__main__':
    try: main()
    except Exception as error:
        raise SystemExit('FAIL: '+str(error))
