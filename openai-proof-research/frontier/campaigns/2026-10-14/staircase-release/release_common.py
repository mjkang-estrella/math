#!/usr/bin/env python3
"""Staircase publication integrity primitives. Copyright 2026 Myeongjin Kang; MIT."""
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import stat
import zipfile

CAMPAIGN = 'frontier/campaigns/2026-10-14'
RELEASE = CAMPAIGN + '/staircase-release'
PAPER = CAMPAIGN + '/staircase-manuscript'
REVIEW = CAMPAIGN + '/staircase-manuscript-review-r1'
PARENT = CAMPAIGN + '/staircase-parent'
FORMAL = CAMPAIGN + '/staircase-formal-v1'
FORMAL_REVIEW = CAMPAIGN + '/staircase-formal-review-r1'
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
FROZEN = {
    PAPER + '/main.tex': '015e76c58ebbd6b92c8868d2de9cf49f533f18408e5017b720df8d02f4767495',
    PAPER + '/main.pdf': '40aebbdda3c407298f499895b7cd8aee543025864efbcb94808441e1b6b6f54c',
    PAPER + '/output-manifest.json': '0fab9a185d016faca5fb035a07aa7b78ddc99dc8437e370f6499897cc989383e',
}
ANCHORS = dict(FROZEN, **{
    FORMAL + '/StaircaseSupport.lean': 'a8a8473d98a673790eb8e72546b890aa93bfba02351a97f401c39d4dbc10e989',
    FORMAL + '/output-manifest.json': '5ff7c5b4e0504d88e1409065129bcef9737160d9484abaa212c7bd69151fd3a0',
    FORMAL_REVIEW + '/review.md': '92b21ed40425c72be41c00a4eb65e2d349b33e8dfeffe3bbb930067cbe30b254',
    FORMAL_REVIEW + '/output-manifest.json': '1d1b217da179bd012e12006f35348ce4c7b3a43fed7a86047db919ea54fd3327',
    PARENT + '/formal-review-disposition.json': '280128251a8b315e51b5b1baa4b843b8c7c981117b81f8db2becd74bce0c8494',
    CAMPAIGN + '/staircase-proof-r1/review.md': '85cdaff75e27300815f81a28fc709a5714b16fa1941d023f44238b302e549e80',
    CAMPAIGN + '/staircase-contribution-factory-r1/review.md': '47de7398e889efb726de5e993384ace4e3e1f83d095e37a68a309f5aaa64b060',
    PAPER + '/inputs/provenance/i21-signed-saxl-dominance.md': '607c2c3296b6e020d8f0ae12526ee593ba3369e00fa5c4f393e53ee5b6936b6a',
})

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def name(value):
    require(isinstance(value, str) and value and '\\' not in value and
            all(ord(ch) >= 32 and ord(ch) != 127 for ch in value),
            'Invalid path')
    p = PurePosixPath(value)
    require(not p.is_absolute() and p.as_posix() == value and
            all(x not in ('', '.', '..') for x in p.parts) and ':' not in value,
            'Noncanonical or escaping path: ' + value)
    return p

def read(root, path):
    p = name(path)
    root = Path(root).absolute()
    require(root.resolve() == root, 'Symlink root is forbidden')
    dest = root
    for part in p.parts:
        dest = dest / part
        require(not dest.is_symlink(), 'Symlink component: ' + path)
    require(dest.is_file(), 'Missing regular file: ' + path)
    return dest.read_bytes()

def no_duplicates(pairs):
    d = {}
    for k, v in pairs:
        require(k not in d, 'Duplicate JSON key: ' + k)
        d[k] = v
    return d

def decode(data):
    return json.loads(data, object_pairs_hook=no_duplicates)

def encode(data):
    return (json.dumps(data, indent=2, sort_keys=True) + '\n').encode()

def record(path, data):
    name(path)
    return {'path': path, 'sha256': sha(data), 'bytes': len(data)}

def valid_record(r):
    require(isinstance(r, dict) and set(r) == {'path', 'sha256', 'bytes'}, 'Malformed record')
    name(r['path'])
    require(isinstance(r['sha256'], str) and re.fullmatch('[0-9a-f]{64}', r['sha256']), 'Invalid digest')
    require(type(r['bytes']) is int and r['bytes'] >= 0, 'Invalid byte length')
    return r

def checked(root, row):
    valid_record(row)
    data = read(root, row['path'])
    require(record(row['path'], data) == row, 'Digest/length mismatch: ' + row['path'])
    return data

def rows_map(rows):
    require(isinstance(rows, list), 'Expected a record list')
    result = {}
    for r in rows:
        valid_record(r)
        require(r['path'] not in result, 'Duplicate member: ' + r['path'])
        result[r['path']] = r
    return result

def manifest_rows(data, prefix):
    obj = decode(data)
    if isinstance(obj, dict):
        keys = set(obj) & {'files', 'outputs'}
        require(len(keys) == 1, 'Manifest must have one files/outputs field')
        obj = obj[next(iter(keys))]
    rows = rows_map(obj)
    result = {}
    for r in rows.values():
        p = r['path']
        if not p.startswith(prefix + '/'):
            require(not p.startswith('frontier/'), 'Foreign manifest path: ' + p)
            p = prefix + '/' + p
        require(p not in result, 'Duplicate normalized member: ' + p)
        result[p] = dict(r, path=p)
    return result

def permitted(path):
    p = name(path)
    require(not set(p.parts) & {'.lake', '__pycache__', '.git', 'external', 'primary', 'packages'},
            'Forbidden payload path: ' + path)
    require(p.suffix not in {'.olean', '.ilean', '.o', '.so', '.zip', '.pyc'}, 'Forbidden binary/archive: ' + path)

def selected(root, path):
    # Preparation freezes foreign artifacts here. Extracted bundles use their final paths.
    if path.startswith(RELEASE + '/'):
        return read(root, path)
    if (Path(root) / RELEASE / 'payload').is_dir():
        return read(Path(root) / RELEASE / 'payload', path)
    return read(root, path)

def frozen_selection(root):
    allow = decode(read(root, RELEASE + '/allowlist.json'))
    rows = rows_map(allow['files'])
    for p, r in rows.items():
        permitted(p)
        data = selected(root, p)
        require(record(p, data) == r, 'Frozen selection differs: ' + p)
    for p, h in ANCHORS.items():
        require(p in rows and rows[p]['sha256'] == h, 'Missing/changed trust anchor: ' + p)
    # Historical output manifests authenticate selected members, not omitted dependencies.
    for prefix, mf in [(PAPER, 'output-manifest.json'), (FORMAL, 'output-manifest.json'),
                       (FORMAL_REVIEW, 'output-manifest.json'),
                       (CAMPAIGN + '/staircase-proof-r1', 'output-manifest.json'),
                       (CAMPAIGN + '/staircase-contribution-factory-r1', 'outputs.json')]:
        members = manifest_rows(selected(root, prefix + '/' + mf), prefix)
        for p, r in rows.items():
            if p.startswith(prefix + '/') and p != prefix + '/' + mf:
                require(members.get(p) == r, 'Selected file absent/different in historical manifest: ' + p)
    require(selected(root, FORMAL_REVIEW + '/context/main.tex') == selected(root, PAPER + '/main.tex'),
            'Formal correspondence snapshot differs')
    return rows

def owned_selection(root):
    manifest_path = RELEASE + '/output-manifest.json'
    data = read(root, manifest_path)
    rows = rows_map(decode(data)['files'])
    for p, r in rows.items():
        require(p.startswith(RELEASE + '/') and '/' not in p[len(RELEASE)+1:], 'Invalid owned output path')
        checked(root, r)
    require(manifest_path not in rows, 'Self hashing manifest')
    rows[manifest_path] = record(manifest_path, data)
    return rows

def gate_records(root, gate_path, trusted):
    require(isinstance(trusted, str) and re.fullmatch('[0-9a-f]{64}', trusted),
            'Independently trusted parent disposition SHA256 is required')
    require(gate_path.startswith(PARENT + '/') and 'manuscript' in name(gate_path).name and
            name(gate_path).suffix == '.json',
            'Gate config must be a separate parent manuscript record')
    raw = read(root, gate_path)
    g = decode(raw)
    require(g.get('schema') == 'staircase-release-gate-v1' and g.get('state') == 'integrated',
            'Final manuscript gate is pending or invalid; cannot assemble')
    require(g.get('bound_paper') == FROZEN, 'Gate is not bound to exact frozen paper hashes')
    pd = valid_record(g['parent_disposition'])
    require(pd['path'].startswith(PARENT + '/') and 'manuscript' in name(pd['path']).name and
            name(pd['path']).suffix == '.json' and
            pd['sha256'] == trusted, 'Parent disposition path/hash is not trusted')
    d = decode(checked(root, pd))
    require(d.get('schema') == 'staircase-manuscript-parent-disposition-v1' and
            d.get('authority') == 'parent integration' and d.get('manuscript_verdict') == 'PASS' and
            d.get('full_original_scope') is True and d.get('required_repairs') == [] and
            d.get('bound_paper') == FROZEN, 'No full-scope integrated parent PASS')
    for k in ['review', 'review_manifest', 'reviewer_record', 'reviewer', 'reviewer_identity_basis']:
        require(g[k] == d[k], 'Parent/config binding differs: ' + k)
    require(set(g['reviewer']) == {'provider', 'model', 'task_id'} and
            all(isinstance(v, str) and v.strip() for v in g['reviewer'].values()), 'Actual reviewer provenance missing')
    require(isinstance(g['reviewer_identity_basis'], str) and g['reviewer_identity_basis'].strip(),
            'Identity-to-artifact provenance explanation required')
    rv, mf, identity = [valid_record(g[k]) for k in ['review', 'review_manifest', 'reviewer_record']]
    require(rv['path'] == REVIEW + '/review.md' and mf['path'].startswith(REVIEW + '/') and
            name(mf['path']).suffix == '.json', 'Unexpected final reviewer artifact/manifest')
    members = manifest_rows(checked(root, mf), REVIEW)
    require(mf['path'] not in members, 'Self hashing review manifest')
    extras = rows_map(g['review_artifacts'])
    requested = {rv['path']: rv, identity['path']: identity}
    require(rv['path'] != identity['path'] or rv == identity, 'Conflicting identity record')
    require(not set(extras) & set(requested), 'Duplicate review selection')
    requested.update(extras)
    for p, r in requested.items():
        require(p.startswith(REVIEW + '/') and members.get(p) == r,
                'Review artifact lacks exact manifest membership: ' + p)
        permitted(p)
        require(name(p).suffix in {'.md', '.json', '.txt', '.py', '.tex', '.lean', '.log', '.png'},
                'Unsupported review artifact type')
        checked(root, r)
    result = dict(requested)
    for r in [mf, pd, record(gate_path, raw)]:
        permitted(r['path'])
        require(r['path'] not in result, 'Duplicate gate evidence')
        result[r['path']] = r
    return result

def archive_write(path, contents):
    require('BUNDLE-MANIFEST.json' in contents, 'Missing archive inventory')
    for p in contents:
        name(p)
    # Exclusive destination, stable order, stored compression, fixed metadata.
    path = Path(path)
    require(not path.is_symlink() and path.parent.resolve() == path.parent.absolute(), 'Symlink output path')
    with path.open('xb') as stream:
        with zipfile.ZipFile(stream, 'w', compression=zipfile.ZIP_STORED) as z:
            for p, data in sorted(contents.items()):
                info = zipfile.ZipInfo(p, (1980, 1, 1, 0, 0, 0))
                info.create_system = 3
                info.external_attr = (stat.S_IFREG | 0o644) << 16
                info.compress_type = zipfile.ZIP_STORED
                z.writestr(info, data)

def archive_read(path):
    result = {}
    with zipfile.ZipFile(path) as z:
        for info in z.infolist():
            p = info.filename
            name(p)
            require(p not in result, 'Duplicate ZIP member: ' + p)
            mode = info.external_attr >> 16
            require(not info.is_dir() and stat.S_IFMT(mode) in {0, stat.S_IFREG},
                    'ZIP symlink/special file: ' + p)
            require(not info.flag_bits & 1, 'Encrypted ZIP member')
            result[p] = z.read(info)
    require('BUNDLE-MANIFEST.json' in result, 'Missing bundle inventory')
    return result
