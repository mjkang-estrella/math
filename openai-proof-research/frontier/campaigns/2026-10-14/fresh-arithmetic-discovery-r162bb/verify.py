#!/usr/bin/env python3
"""Read-only exact packet verification; all three detached anchors are mandatory."""
import argparse, hashlib, json, os, re, stat
from pathlib import Path, PurePosixPath

def need(ok, message):
    if not ok: raise ValueError(message)

def safe(s):
    need(isinstance(s,str) and s and chr(92) not in s and chr(0) not in s, 'unsafe path')
    p=PurePosixPath(s)
    need(not p.is_absolute() and str(p)==s and all(t not in ('.','..') for t in p.parts), 'unsafe path')
    return s

def pairs(xs):
    need(len({k for k,v in xs})==len(xs), 'duplicate JSON key')
    return dict(xs)

def readjson(p): return json.loads(p.read_bytes(),object_pairs_hook=pairs)
def digest(b): return hashlib.sha256(b).hexdigest()
def mode(p): return stat.S_IMODE(p.lstat().st_mode)

def verify(root, anchors):
    root=Path(root)
    need(root.is_dir() and not root.is_symlink(), 'unsafe root')
    root=root.resolve()
    detached={'private/FINAL.md':anchors[0],'private/MANIFEST.json':anchors[1],'REPORT.md':anchors[2]}
    for name,h in detached.items():
        need(re.fullmatch('[0-9a-f]{64}',h) is not None,'invalid explicit anchor')
        p=root/name
        need(p.is_file() and not p.is_symlink(),'missing detached file')
        need(digest(p.read_bytes())==h,'detached anchor mismatch: '+name)
    m=readjson(root/'private/MANIFEST.json')
    need(m['schema']=='r162bb-packet-v1','manifest schema')
    need(mode(root)==m['root_mode'],'root mode')
    records=m['files']; directories=m['directories']
    fp=[safe(e['path']) for e in records]; dp=[safe(e['path']) for e in directories]
    need(fp==sorted(fp) and len(fp)==len(set(fp)),'file records not sorted unique')
    need(dp==sorted(dp) and len(dp)==len(set(dp)),'directory records not sorted unique')
    names=fp+dp+list(detached)
    need(len({s.casefold() for s in names})==len(names),'duplicate or case-colliding membership')
    actual_f=set();actual_d=set()
    for base,ds,fs in os.walk(root,followlinks=False):
        for n in ds:
            p=Path(base)/n;need(p.is_dir() and not p.is_symlink(),'unsafe directory')
            actual_d.add(p.relative_to(root).as_posix())
        for n in fs:
            p=Path(base)/n;s=p.lstat()
            need(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'nonregular, symbolic or hard-linked file')
            actual_f.add(p.relative_to(root).as_posix())
    need(actual_f==set(fp)|set(detached),'exact file membership mismatch')
    need(actual_d==set(dp),'exact directory membership mismatch')
    for e in directories: need(mode(root/e['path'])==e['mode'],'directory mode mismatch')
    for e in records:
        p=root/e['path'];b=p.read_bytes()
        need(len(b)==e['bytes'] and digest(b)==e['sha256'],'payload bytes mismatch: '+e['path'])
        need(mode(p)==e['mode'],'payload mode mismatch: '+e['path'])
    for s in detached: need(mode(root/s)==(0o644 if s=='REPORT.md' else 0o600),'detached mode mismatch')
    # Authenticate only own canonical and completed copies; no original namespace is read.
    ap=root/'private/authentication.json'
    if ap.exists():
        auth=readjson(ap); meta=readjson(root/'private/selected-metadata.json')
        mb={safe(e['path']):e for e in meta if e['type']=='blob'}
        need(len(mb)==len(auth)==43 and len(meta)==55,'selected canonical membership')
        need(len({e['path'] for e in auth})==43,'duplicate canonical record')
        for e in auth:
            s=safe(e['path']);p=root/'private/source'/s;b=p.read_bytes();z=mb[s]
            need(e['size']==z['size']==len(b) and e['sha']==z['sha'],'canonical metadata mismatch')
            need(e['mode']==z['mode']=='100644','canonical upstream mode')
            need(hashlib.sha1(b'blob '+str(len(b)).encode()+bytes([0])+b).hexdigest()==e['sha'],'canonical Git blob mismatch')
            need(digest(b)==e['sha256'],'canonical SHA256 mismatch')
        copies=readjson(root/'private/exception-copies.json')
        need(len(copies)==5 and len({e['copy'] for e in copies})==5,'completed copy membership')
        for e in copies:
            p=root/safe(e['copy']);b=p.read_bytes()
            need(len(b)==e['length'] and digest(b)==e['sha256'],'completed copy mismatch')
    return {'payload_files':len(fp),'whole_root_files':len(actual_f),'subdirectories':len(actual_d),'artifact_verification':'passed; not a mathematical gate'}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',required=True)
    p.add_argument('--final-sha256',required=True)
    p.add_argument('--manifest-sha256',required=True)
    p.add_argument('--report-sha256',required=True)
    a=p.parse_args()
    print(json.dumps(verify(a.root,[a.final_sha256,a.manifest_sha256,a.report_sha256]),sort_keys=True))
if __name__=='__main__': main()
