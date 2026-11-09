#!/usr/bin/env python3
"""Read-only exact packet verifier. Supply detached SHA256 anchors explicitly."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat

DETACHED = {'MANIFEST.json', 'REPORT.md'}
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
MASTER = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'

def digest(b):
    return hashlib.sha256(b).hexdigest()

def safe(s):
    assert isinstance(s, str) and s and '\\' not in s and '\x00' not in s
    p = PurePosixPath(s)
    assert not p.is_absolute() and all(x not in ('', '.', '..') for x in p.parts)
    assert str(p) == s
    return s

def inventory(root, exclude=()):
    root = Path(root)
    st = root.lstat()
    assert stat.S_ISDIR(st.st_mode) and not root.is_symlink()
    dirs, files = [], []
    def descend(base):
        for entry in sorted(os.scandir(base), key=lambda e:e.name):
            path = Path(entry.path)
            rel = safe(path.relative_to(root).as_posix())
            s = path.lstat()
            assert not stat.S_ISLNK(s.st_mode), rel
            if stat.S_ISDIR(s.st_mode):
                dirs.append({'path':rel, 'mode':s.st_mode})
                descend(path)
            else:
                assert stat.S_ISREG(s.st_mode) and s.st_nlink == 1, rel
                if rel in exclude:
                    continue
                b = path.read_bytes()
                files.append({'path':rel, 'mode':s.st_mode, 'bytes':len(b), 'sha256':digest(b)})
    descend(root)
    return {'root_mode':st.st_mode, 'directories':sorted(dirs,key=lambda x:x['path']),
            'files':sorted(files,key=lambda x:x['path'])}

def check_records(root, expected, exclude=()):
    for key in ('directories', 'files'):
        names = [safe(x['path']) for x in expected[key]]
        assert names == sorted(set(names)), 'nonunique or unsorted '+key
    assert inventory(root, exclude) == {k:expected[k] for k in ('root_mode','directories','files')}, 'inventory/hash/length/full-mode mismatch'

def anchor(path, expected):
    assert len(expected)==64 and all(c in '0123456789abcdef' for c in expected), 'invalid explicit anchor'
    assert digest(Path(path).read_bytes()) == expected, 'detached anchor mismatch: '+str(path)

def bindings(root, project):
    entries = json.loads((root/'private/source-tree.json').read_text())
    master_bytes = (project/'sources/preprints-tree.json').read_bytes()
    assert digest(master_bytes) == MASTER
    master = json.loads(master_bytes)
    assert len(master['tree']) == 13223 and master.get('truncated') is False
    master_by = {e['path']:e for e in master['tree']}
    assert all(master_by[e['path']] == e for e in entries)
    assert len(entries)==7 and sum(e['type']=='blob' for e in entries)==5
    assert json.loads((project/'sources/upstream.json').read_text())['commit'] == PIN
    by_path = {e['path']:e for e in entries}
    recs = json.loads((root/'private/bindings.json').read_text())
    originals = 0
    for rec in recs:
        copied = root/safe(rec['copy'])
        b = copied.read_bytes()
        assert len(b)==rec['bytes'] and digest(b)==rec['sha256']
        if 'git_blob' in rec:
            e = by_path[rec['path']]
            assert e['size']==len(b) and e['sha']==rec['git_blob']
            assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['sha']
            assert rec['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+rec['path']
        else:
            originals += 1
            original = project/safe(rec['path'])
            assert original.lstat().st_mode==rec['mode']==copied.lstat().st_mode
            assert original.read_bytes()==b
    assert originals==5 and len(recs)==10
    # Authenticate both selected Git tree objects without accessing git state.
    for parent in [e for e in entries if e['type']=='tree']:
        children = [e for e in entries if str(PurePosixPath(e['path']).parent)==parent['path']]
        children.sort(key=lambda e:PurePosixPath(e['path']).name+('/' if e['type']=='tree' else ''))
        body=b''.join((e['mode'].lstrip('0')+' '+PurePosixPath(e['path']).name).encode()+b'\0'+bytes.fromhex(e['sha']) for e in children)
        assert hashlib.sha1(b'tree '+str(len(body)).encode()+b'\0'+body).hexdigest()==parent['sha']
    primary=json.loads((root/'private/primary/reading.json').read_text())
    for rec in primary['files']:
        p=root/safe(rec['path']); b=p.read_bytes()
        assert len(b)==rec['bytes'] and digest(b)==rec['sha256']
    return originals

def verify(root, project, final_sha, manifest_sha, report_sha):
    root=Path(root); project=Path(project)
    anchor(root/'FINAL.md',final_sha)
    anchor(root/'MANIFEST.json',manifest_sha)
    anchor(root/'REPORT.md',report_sha)
    m=json.loads((root/'MANIFEST.json').read_text())
    assert m['version']==1 and m['pin']==PIN
    check_records(root,m,DETACHED)
    for name in DETACHED:
        assert (root/name).lstat().st_mode==m['detached_modes'][name]
    assert next(x['sha256'] for x in m['files'] if x['path']=='FINAL.md')==final_sha
    bindings(root,project)
    return {'status':'MATCH','payloads':len(m['files']), 'bytes':sum(x['bytes'] for x in m['files']),
            'files':len(m['files'])+2,'directories_including_root':len(m['directories'])+1}

if __name__=='__main__':
    a=argparse.ArgumentParser()
    for name in ('root','project','final-sha','manifest-sha','report-sha'):
        a.add_argument('--'+name,required=True)
    x=a.parse_args()
    print(json.dumps(verify(x.root,x.project,x.final_sha,x.manifest_sha,x.report_sha),sort_keys=True))
