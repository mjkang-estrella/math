#!/usr/bin/env python3
"""Read-only packet verifier. Detached anchors must be supplied explicitly."""
import argparse, hashlib, json, os, stat
from pathlib import Path, PurePosixPath

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
PREFIX = 'preprints/The-hypercube-Ramsey-number-has-linear-order-September-23-2026'
TREE_DIGEST = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
ORIGINALS = [
 'frontier/campaigns/2026-10-14/discovery-arithmetic-r162ci-parent/assessment.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ci/private/DERIVATION.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ci/private/WORKING.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ci/private/READING-LIMITS.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ci/FINAL.md']
RESERVED = {'MANIFEST.json', 'REPORT.md'}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def safe(name):
    assert isinstance(name, str) and name and '\\' not in name
    p = PurePosixPath(name)
    assert not p.is_absolute() and p.as_posix() == name
    assert all(s not in ('', '.', '..') for s in p.parts)
    return name

def require_hash(data, expected):
    assert len(expected) == 64 and all(c in '0123456789abcdef' for c in expected)
    assert sha(data) == expected, 'detached/hash mismatch'

def inventory(root):
    files, dirs = {}, {}
    assert stat.S_ISDIR(root.lstat().st_mode) and not root.is_symlink()
    for base, children, names in os.walk(root, followlinks=False):
        b = Path(base)
        rel = b.relative_to(root).as_posix()
        dirs[rel] = b.lstat().st_mode
        for name in children:
            q = b/name
            assert stat.S_ISDIR(q.lstat().st_mode) and not q.is_symlink(), 'unsafe directory'
        for name in names:
            q = b/name
            assert stat.S_ISREG(q.lstat().st_mode) and not q.is_symlink(), 'unsafe file'
            files[safe(q.relative_to(root).as_posix())] = q.lstat().st_mode
    return files, dirs

def check_inventory(root, manifest, virtual=None):
    virtual = virtual or {}
    files, dirs = inventory(root)
    for name, data in virtual.items():
        assert name in RESERVED and name not in files
        files[name] = 0o100644
    rows = manifest['files']; dr = manifest['directories']
    paths = [safe(x['path']) for x in rows]
    dpaths = [x['path'] for x in dr]
    assert paths == sorted(paths) and len(paths) == len(set(paths)), 'file ordering/uniqueness'
    assert dpaths == sorted(dpaths) and len(dpaths) == len(set(dpaths)), 'directory ordering/uniqueness'
    assert set(paths) == set(files)-RESERVED, 'exact file membership'
    assert set(dpaths) == set(dirs), 'exact directory membership'
    for x in dr:
        if x['path'] != '.': safe(x['path'])
        assert dirs[x['path']] == x['mode'], 'full directory mode'
    for x in rows:
        data = (root/x['path']).read_bytes()
        assert len(data) == x['bytes'] and files[x['path']] == x['mode'], 'length/full file mode'
        require_hash(data, x['sha256'])
    return len(rows), len(dr)

def check_bindings(root, project):
    entries = json.loads((root/'private/source-tree.json').read_bytes())
    bindings = json.loads((root/'private/source-bindings.json').read_bytes())
    assert len(entries) == 31 and len(bindings) == 27
    ep = [x['path'] for x in entries]
    assert len(ep) == len(set(ep))
    assert all(x == PREFIX or x.startswith(PREFIX+'/') for x in ep)
    em = {x['path']: x for x in entries}
    assert em[PREFIX]['sha'] == 'e09247960617d7cc7e76e30f783c45595b4de9c5'
    assert em[PREFIX+'/build/main.tex']['sha'] == '2f4bc380a47867c1cb6268ef999b8ac1175ed920'
    assert [x['path'] for x in bindings] == sorted(x['path'] for x in bindings)
    assert {x['upstream'] for x in bindings} == {x['path'] for x in entries if x['type']=='blob'}
    for b in bindings:
        e = em[b['upstream']]
        rel = 'private/source/'+b['upstream'][len(PREFIX)+1:]
        assert b['path'] == rel
        assert b['url'] == 'https://raw.githubusercontent.com/openai/math/'+PIN+'/'+b['upstream']
        f = root/safe(rel); data = f.read_bytes()
        assert len(data) == b['bytes'] == e['size']
        require_hash(data, b['sha256'])
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest() == b['git_blob'] == e['sha']
        assert f.lstat().st_mode == int(e['mode'],8)
    trees = [x for x in entries if x['type']=='tree']; assert len(trees) == 4
    for e in trees:
        kids = [x for x in entries if str(PurePosixPath(x['path']).parent)==e['path']]
        kids.sort(key=lambda x: PurePosixPath(x['path']).name+('/' if x['type']=='tree' else ''))
        data = b''.join(x['mode'].lstrip('0').encode()+b' '+PurePosixPath(x['path']).name.encode()+b'\0'+bytes.fromhex(x['sha']) for x in kids)
        assert hashlib.sha1(b'tree '+str(len(data)).encode()+b'\0'+data).hexdigest() == e['sha']
    copies = json.loads((root/'private/completed-bindings.json').read_bytes())
    assert [x['original'] for x in copies] == ORIGINALS
    for i,b in enumerate(copies):
        assert b['copy'] == 'private/completed/'+str(i)
        original = project/b['original']; copied = root/b['copy']
        assert stat.S_ISREG(original.lstat().st_mode) and not original.is_symlink()
        data = original.read_bytes()
        assert data == copied.read_bytes() and len(data) == b['bytes']
        require_hash(data,b['sha256'])
        assert original.lstat().st_mode == b['full_mode'] == copied.lstat().st_mode
        assert stat.S_IMODE(original.lstat().st_mode) == b['mode']
    control_source=(root/'private/source/build/sections/proof-inputs.tex').read_bytes()
    for name in ['a.bin','b.bin']:
        assert (root/('private/integrity-controls/'+name)).read_bytes()==control_source
    for b in json.loads((root/'private/primary-bindings.json').read_bytes()):
        if 'error' in b: continue
        data=(root/('private/primary/'+b['name']+'.pdf')).read_bytes()
        assert len(data)==b['bytes'];require_hash(data,b['sha256'])

def verify_packet(root, project, final_sha, manifest_sha, report_sha, virtual=None):
    virtual = virtual or {}
    def read(name): return virtual[name] if name in virtual else (root/name).read_bytes()
    require_hash(read('FINAL.md'),final_sha)
    require_hash(read('MANIFEST.json'),manifest_sha)
    require_hash(read('REPORT.md'),report_sha)
    for name in RESERVED:
        assert (0o100644 if name in virtual else (root/name).lstat().st_mode)==0o100644
    m=json.loads(read('MANIFEST.json'))
    assert m['pin']==PIN and m['complete_tree_sha256']==TREE_DIGEST
    assert m['reserved']==sorted(RESERVED)
    counts=check_inventory(root,m,virtual)
    check_bindings(root,project)
    return counts

if __name__=='__main__':
    a=argparse.ArgumentParser(description=__doc__)
    for flag in ['root','project','final-sha256','manifest-sha256','report-sha256']: a.add_argument('--'+flag,required=True)
    x=a.parse_args()
    counts=verify_packet(Path(x.root),Path(x.project),x.final_sha256,x.manifest_sha256,x.report_sha256)
    print('MATCH: %d payload files; %d directories including root; pinned blobs/trees and five original/copy pairs unchanged. Artifact check only.' % counts)
