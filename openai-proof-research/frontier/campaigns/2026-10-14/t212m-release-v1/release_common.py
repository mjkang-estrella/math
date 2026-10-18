#!/usr/bin/env python3
"""T212M release identity helpers, adapted from checked T117Q/preparation helpers.
Copyright 2026 Myeongjin Kang. MIT. Identity checks are not mathematical gates.
"""
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import zipfile

OWN = ['release_common.py', 'final_release.py', 'replay_release.py',
       'reproduce_supplement.py', 'public-selection-final-draft.json',
       'release-policy.json', 'RELEASE-README.md']
R1 = 'c7942e070a2e01f03d27790f60d6225326f8f563a9364518f54a51cd3b9b3a99'
MANUSCRIPT = 'c71b20126326de8eab4d016b92cca78c9e43440653361899a8335fc2747c7b3f'

def require(ok, why):
    if not ok:
        raise ValueError(why)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def pairs(items):
    out = {}
    for key, value in items:
        require(key not in out, 'duplicate JSON key')
        out[key] = value
    return out

def parse(raw):
    return json.loads(raw, object_pairs_hook=pairs)

def anchor(value):
    require(isinstance(value, str) and len(value) == 64 and
            all(c in '0123456789abcdef' for c in value), 'malformed external anchor')

def safe(name):
    require(isinstance(name, str), 'non-string path')
    p = PurePosixPath(name)
    require(name and name != '.' and name == p.as_posix() and not p.is_absolute()
            and '..' not in p.parts and '\\' not in name and ':' not in name,
            'unsafe relative path')
    return p

def public(name):
    p = safe(name)
    require(not any(x in ('private', '.lake', '__pycache__', 'node_modules', '.git', 'cache')
                    for x in p.parts), 'private/cache payload')
    require(not name.endswith(('.olean', '.ilean', '.o', '.so', '.pyc',
                               '/seal.py', '/run_review.py', '/review_controls.py')),
            'compiled/cache or write-in-place driver')

def ancestry(path):
    require(path.is_absolute() and '..' not in path.parts, 'absolute normalized path required')
    for p in reversed(path.parents):
        require(stat.S_ISDIR(p.lstat().st_mode), 'unsafe root ancestry')

def read(root, name):
    p = root.joinpath(*safe(name).parts)
    ancestry(p)
    st = p.lstat()
    require(stat.S_ISREG(st.st_mode) and st.st_nlink == 1, 'nonregular or hardlinked file')
    return p.read_bytes()

def tree(root):
    ancestry(root)
    require(stat.S_ISDIR(root.lstat().st_mode), 'non-directory root')
    files, dirs = {}, []
    def walk(base):
        for e in os.scandir(base):
            p = Path(e.path); name = p.relative_to(root).as_posix(); st = p.lstat()
            if stat.S_ISDIR(st.st_mode):
                dirs.append(name); walk(p)
            else:
                require(stat.S_ISREG(st.st_mode) and st.st_nlink == 1,
                        'nonregular, linked or hardlinked tree entry')
                files[name] = read(root, name)
    walk(root)
    return files, sorted(dirs)

def dirs_for(names):
    return sorted({str(q) for n in names for q in safe(n).parents if str(q) != '.'})

def record(data):
    return {'bytes': len(data), 'sha256': sha(data)}

def check(data, row):
    require(record(data) == {'bytes': row['bytes'], 'sha256': row['sha256']},
            'selected size/hash mismatch')

def member_hash(manifest, name):
    entries = manifest['files']
    if isinstance(entries, list):
        require(len({r['path'] for r in entries}) == len(entries), 'duplicate frozen member')
        entries = {r['path']: r for r in entries}
    rec = entries.get(name)
    require(rec is not None, 'missing frozen member')
    return rec if isinstance(rec, str) else rec['sha256']

def implementation(get, expected):
    anchor(expected)
    raw = get('IMPLEMENTATION-MANIFEST.json')
    require(sha(raw) == expected, 'external implementation anchor mismatch')
    m = parse(raw)
    require(set(m) == {'schema', 'files'} and m['schema'] == 'T212M-release-tools-v1',
            'implementation schema')
    require(set(m['files']) == set(OWN), 'implementation exact helper set')
    for name in OWN:
        check(get(name), m['files'][name])
    policy = parse(get('release-policy.json'))
    require(policy['schema'] == 'T212M-release-policy-v1', 'release policy schema')
    require(policy['source_pin'] == 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
            and policy['manuscript_anchor'] == MANUSCRIPT and policy['r1_anchor'] == R1,
            'T212M fixed source/manuscript/r1 anchors')
    require(policy['accepted'] is False and policy['published'] is False and
            policy['count_change'] == 0 and policy['full_theorem_formalized'] is False,
            'unsupported acceptance/formal status')
    raw_selection = get('public-selection-final-draft.json')
    require(sha(raw_selection) == policy['selection_sha256'], 'selection policy binding')
    return policy, parse(raw_selection)

def completion(policy, r2_anchor, closure_anchor):
    c = policy['completion']
    require(c is not None, 'actual r2 review and parent closure are pending')
    anchor(r2_anchor); anchor(closure_anchor)
    require(c['r2']['packet'] == 't212m-manuscript-review-r2', 'wrong r2 packet')
    require(c['r2']['sha256'] == r2_anchor and c['parent']['sha256'] == closure_anchor,
            'external r2/closure anchor mismatch')
    require(c['parent']['path'].startswith('t212m-parent/'), 'wrong parent closure location')
    public(c['parent']['path'])
    return c

def validate_inputs(get, selection, policy, final=False, r2_anchor=None, closure_anchor=None):
    anchors = dict(selection['anchors']); rows = list(selection['files'])
    c = None
    if final:
        c = completion(policy, r2_anchor, closure_anchor)
        anchors[c['r2']['packet']] = {k:c['r2'][k] for k in ('manifest', 'sha256')}
        rows += c['files'] + [dict(c['parent'], packet=None)]
    manifests = {}
    for packet, a in anchors.items():
        safe(packet); safe(a['manifest']); anchor(a['sha256'])
        raw = get(packet + '/' + a['manifest'])
        require(sha(raw) == a['sha256'], 'frozen manifest anchor mismatch')
        manifests[packet] = parse(raw)
    names = set()
    for row in rows:
        name = row['path']; public(name)
        require(name not in names, 'duplicate selected file'); names.add(name)
        data = get(name); check(data, row)
        packet = row['packet']
        if packet:
            require(name == packet + '/' + row['relative'], 'packet/relative mismatch')
            if row['relative'] != anchors[packet]['manifest']:
                require(member_hash(manifests[packet], row['relative']) == row['sha256'],
                        'selected file not bound by frozen manifest')
        else:
            require(name.startswith('t212m-parent/'), 'unbound non-packet evidence')
    for packet, a in anchors.items():
        require(packet + '/' + a['manifest'] in names, 'unselected frozen anchor')
    r1 = manifests['t212m-manuscript-review-r1']
    require(r1['verdict'] == 'PASS_FULL_MANUSCRIPT_T212M' and
            r1['manuscript_anchor'] == MANUSCRIPT and r1['required_objections'] == 0,
            'r1 manuscript verdict binding')
    require('t212m-formal-review-r1/independent-logs/Independent.lean.log' in names,
            'missing independent replay reference log')
    if c:
        rm = manifests[c['r2']['packet']]
        require(rm.get('verdict') == 'PASS_AH_PROOF_INTERFACES_T212M' and
                type(rm.get('required_objections')) is int and rm['required_objections'] == 0 and
                rm.get('manuscript_anchor') == MANUSCRIPT,
                'r2 operative-interface verdict/zero objections/manuscript binding required')
        metadata = {k:v for k,v in rm.items() if k not in ('files', 'directories')}
        require(metadata == c['r2']['expected_metadata'], 'actual r2 metadata mismatch')
        require(c['r2']['sha256'] != R1, 'r1 cannot substitute for r2')
        parent = parse(get(c['parent']['path']))
        require(parent == c['parent']['expected_content'], 'exact parent closure changed')
        required = {'status':'ADOPTED_FULL_MANUSCRIPT_CLOSURE_T212M',
                    'manuscript_anchor':MANUSCRIPT, 'r1_review_anchor':R1,
                    'r2_review_anchor':r2_anchor, 'closure_complete':True,
                    'accepted':False, 'published':False, 'count_change':0}
        require(all(parent.get(k) == v and type(parent.get(k)) is type(v)
                    for k,v in required.items()), 'parent manuscript closure incomplete')
        require(all(r['packet'] == c['r2']['packet'] for r in c['files']),
                'unexpected completion payload')
        for name in ('review.md', 'reading-limits.md'):
            require(c['r2']['packet'] + '/' + name in names, 'missing actual r2 report/limits')
    return rows

def new_output(path, inputs):
    ancestry(path)
    require(not path.exists() and not path.is_symlink(), 'output must be new')
    require(all(not path.is_relative_to(p) and not p.is_relative_to(path) for p in inputs),
            'output overlaps inputs')

def stable_zip(path, payload):
    with zipfile.ZipFile(path, 'x', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        z.comment = b''
        for name, data in sorted(payload.items()):
            public(name)
            info = zipfile.ZipInfo(name, (2026,10,18,0,0,0))
            info.create_system = 3; info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16; info.internal_attr = 0
            info.extra = b''; info.comment = b''
            z.writestr(info, data, compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)

def zip_payload(path):
    read(path.parent, path.name)  # reject unsafe container ancestry/type before opening
    with zipfile.ZipFile(path) as z:
        names = z.namelist()
        require(names == sorted(set(names)) and z.comment == b'', 'ZIP order/duplicates/comment')
        for i in z.infolist():
            public(i.filename)
            require(not i.is_dir() and i.create_system == 3 and i.external_attr == 0o100644 << 16
                    and i.internal_attr == 0 and i.date_time == (2026,10,18,0,0,0)
                    and i.compress_type == zipfile.ZIP_DEFLATED and not i.extra and not i.comment
                    and i.flag_bits == 0, 'noncanonical or unsafe ZIP member')
        return {name:z.read(name) for name in names}
