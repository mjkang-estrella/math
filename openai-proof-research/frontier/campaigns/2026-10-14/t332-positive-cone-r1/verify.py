#!/usr/bin/env python3
"""Externally anchored exact inventory; not a proof. Original code MIT."""
import argparse,hashlib,json,os,stat
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def unique(xs):
    r={}
    for k,v in xs:
        if k in r:raise ValueError('duplicate key')
        r[k]=v
    return r

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--manifest-sha256',required=True);ap.add_argument('--verifier-sha256',required=True);a=ap.parse_args()
    script=Path(os.path.abspath(__file__))
    for p in [*reversed(script.parents),script]:
        st=p.lstat()
        if stat.S_ISLNK(st.st_mode):raise ValueError('ancestor/root/script symlink')
    base=script.parent;files=set();dirs=set()
    def walk(p):
        for e in os.scandir(p):
            q=Path(e.path);s=q.lstat();r=q.relative_to(base).as_posix()
            if stat.S_ISDIR(s.st_mode):dirs.add(r);walk(q)
            elif stat.S_ISREG(s.st_mode):
                if s.st_nlink!=1:raise ValueError('hardlink')
                files.add(r)
            else:raise ValueError('symlink or nonregular object')
    walk(base)
    if sha(script)!=a.verifier_sha256:raise ValueError('wrong verifier anchor')
    if sha(base/'manifest.json')!=a.manifest_sha256:raise ValueError('wrong manifest anchor')
    m=json.loads((base/'manifest.json').read_text(),object_pairs_hook=unique)
    if set(m)!={'schema','status','files','directories'} or m['schema']!=1 or m['status']!='UNRESOLVED_T332_ROUTE_ONLY':raise ValueError('schema')
    if set(m['files'])!=files-{'manifest.json'} or set(m['directories'])!=dirs or len(set(m['directories']))!=len(m['directories']):raise ValueError('inventory')
    for r,v in m['files'].items():
        if r.startswith('/') or '\\' in r or any(x in ('','.','..') for x in r.split('/')) or r.endswith('/manifest.json'):raise ValueError('unsafe or nested manifest path')
        p=base/r
        if set(v)!={'bytes','sha256'} or type(v['bytes']) is not int or p.stat().st_size!=v['bytes'] or sha(p)!=v['sha256']:raise ValueError('payload: '+r)
    print(json.dumps({'status':'PASS_INVENTORY_NOT_PROOF','files':len(m['files']),'directories':len(dirs)}))
if __name__=='__main__':
    try:main()
    except (ValueError,OSError,KeyError,TypeError) as e:raise SystemExit('FAIL: '+str(e))
