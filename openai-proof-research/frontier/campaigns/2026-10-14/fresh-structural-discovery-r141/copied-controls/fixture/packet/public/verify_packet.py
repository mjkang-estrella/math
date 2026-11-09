#!/usr/bin/env python3
"""Read-only byte/inventory verifier. Not a mathematical correctness verifier.
Run with python -B and three detached SHA256 values from the handoff.
The exact root inventory excludes only four top-level envelope files;
nested copies of these names are ordinary inventoried payload bytes.
"""
import argparse, hashlib, json, os, pathlib, re, stat, sys
ENVELOPES={'MANIFEST.json','outsideREPORT.md','FINAL.json','ANCHORS.json'}
HEX=re.compile(r'[0-9a-f]{64}\Z')

def digest(b):return hashlib.sha256(b).hexdigest()
def unique(pairs):
    d={}
    for k,v in pairs:
        if k in d:raise ValueError('duplicate JSON key: '+k)
        d[k]=v
    return d

def parsed(b):return json.loads(b,object_pairs_hook=unique)
def regular_bytes(p):
    s=p.lstat()
    if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1:raise ValueError('nonregular or hardlinked file: '+str(p))
    b=p.read_bytes();t=p.lstat()
    if (s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_mode,s.st_nlink)!=(t.st_dev,t.st_ino,t.st_size,t.st_mtime_ns,t.st_mode,t.st_nlink):
        raise ValueError('file changed while read: '+str(p))
    return b,s

def inventory(root):
    entries=[]
    def descend(d):
        for p in sorted(d.iterdir(),key=lambda q:q.name):
            rel=p.relative_to(root).as_posix()
            if '/' not in rel and rel in ENVELOPES:continue
            s=p.lstat();mode=stat.S_IMODE(s.st_mode)
            if stat.S_ISDIR(s.st_mode):
                entries.append({'path':rel,'type':'directory','mode':mode});descend(p)
            elif stat.S_ISREG(s.st_mode):
                b,s=regular_bytes(p)
                entries.append({'path':rel,'type':'file','mode':mode,'size':len(b),'sha256':digest(b)})
            else:raise ValueError('link or nonregular node: '+rel)
    descend(root)
    return sorted(entries,key=lambda x:x['path'])

def verify(root,anchors):
    if root.absolute()!=root.resolve() or not root.is_dir():raise ValueError('root must be a real directory without symlink ancestors')
    envelope={}
    for n in ENVELOPES:
        b,s=regular_bytes(root/n)
        if stat.S_IMODE(s.st_mode)!=0o644:raise ValueError('envelope mode differs from 0644: '+n)
        envelope[n]=b
    for n,h in anchors.items():
        if not HEX.fullmatch(h):raise ValueError('invalid external SHA256')
        if digest(envelope[n])!=h:raise ValueError('external anchor mismatch: '+n)
    if parsed(envelope['ANCHORS.json'])!=anchors:raise ValueError('ANCHORS.json differs from external anchors')
    m=parsed(envelope['MANIFEST.json'])
    if set(m)!={'format','created_utc','root_mode','entries'} or m['format']!='r141-exact-root-v1':raise ValueError('manifest schema')
    if m['root_mode']!=stat.S_IMODE(root.stat().st_mode):raise ValueError('root mode mismatch')
    seen=set()
    for e in m['entries']:
        p=e.get('path');q=pathlib.PurePosixPath(p) if isinstance(p,str) else None
        if not p or q.is_absolute() or any(c in ('','..','.') for c in p.split('/')) or str(q)!=p or p in seen or p in ENVELOPES:
            raise ValueError('unsafe, duplicate or envelope inventory path')
        seen.add(p)
        keys={'path','type','mode'}|({'size','sha256'} if e.get('type')=='file' else set())
        if e.get('type') not in ('file','directory') or set(e)!=keys:raise ValueError('entry schema')
    actual=inventory(root)
    if actual!=m['entries']:raise ValueError('exact inventory/content/mode mismatch')
    f=parsed(envelope['FINAL.json'])
    if f.get('manifest_sha256')!=anchors['MANIFEST.json'] or f.get('outside_report_sha256')!=anchors['outsideREPORT.md']:
        raise ValueError('FINAL bindings mismatch')
    return {'artifact_integrity':'matched detached anchors and exact inventory','files':sum(e['type']=='file' for e in actual),'directories':sum(e['type']=='directory' for e in actual),'entries':len(actual),'mathematical_verdict':None}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',type=pathlib.Path,required=True)
    for k in ('manifest','report','final'):ap.add_argument('--'+k+'-sha256',required=True)
    a=ap.parse_args()
    anchors={'MANIFEST.json':a.manifest_sha256,'outsideREPORT.md':a.report_sha256,'FINAL.json':a.final_sha256}
    try:result=verify(a.root.absolute(),anchors)
    except (ValueError,OSError,TypeError,KeyError,json.JSONDecodeError) as e:
        print(json.dumps({'artifact_integrity':'REJECTED','reason':str(e)}));return 1
    print(json.dumps(result));return 0
if __name__=='__main__':sys.exit(main())
