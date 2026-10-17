#!/usr/bin/env python3
# Original review support; Copyright 2026 Myeongjin Kang. MIT.
"""Read-only exact membership and external-anchor verifier, not a mathematical checker."""
import argparse, hashlib, json, os, re, stat
from pathlib import Path, PurePosixPath

def need(x,msg):
    if not x: raise ValueError(msg)
def digest(data): return hashlib.sha256(data).hexdigest()
def unique(pairs):
    d={}
    for k,v in pairs:
        need(k not in d,'duplicate JSON key');d[k]=v
    return d
def parse(raw): return json.loads(raw,object_pairs_hook=unique)
def safe(name):
    need(isinstance(name,str) and name and '\\' not in name,'invalid path')
    p=PurePosixPath(name)
    need(not p.is_absolute() and p.as_posix()==name and all(s not in ('','.','..') for s in p.parts),'unsafe path')
    return name
def inventory(root,mname,anchor):
    need(re.fullmatch('[0-9a-f]{64}',anchor) is not None,'bad anchor')
    need(root.is_dir() and not root.is_symlink(),'invalid root')
    mp=root/safe(mname);need(not mp.is_symlink(),'manifest symlink')
    raw=mp.read_bytes();need(digest(raw)==anchor,'external anchor mismatch')
    m=parse(raw);rows=m['files']
    if isinstance(rows,dict):rows=[dict(path=k,sha256=v) for k,v in rows.items()]
    expected={}
    for row in rows:
        n=safe(row['path']);need(n!=mname and n not in expected,'duplicate/self payload');expected[n]=row
        need(re.fullmatch('[0-9a-f]{64}',row['sha256']) is not None,'bad hash')
    wanted=[safe(p) for p in m['directories']];need(len(wanted)==len(set(wanted)),'duplicate directory')
    files=set();dirs=set()
    for folder,ds,fs in os.walk(root,followlinks=False):
        for n in ds+fs:
            p=Path(folder)/n;rel=safe(p.relative_to(root).as_posix());mode=p.lstat().st_mode
            need(not stat.S_ISLNK(mode),'symlink')
            if stat.S_ISDIR(mode):dirs.add(rel)
            else:need(stat.S_ISREG(mode),'nonregular file');files.add(rel)
    need(files==set(expected)|{mname},'exact file membership')
    need(dirs==set(wanted),'exact directory membership')
    for n,row in expected.items():
        raw=(root/n).read_bytes();need(digest(raw)==row['sha256'],'changed payload: '+n)
        if 'bytes' in row:need(len(raw)==row['bytes'],'wrong payload size')
    return m,len(expected),len(dirs)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--anchor',required=True);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--campaign-root',type=Path,default=Path(__file__).resolve().parent.parent);a=ap.parse_args()
    m,n,d=inventory(a.root,'output-manifest.json',a.anchor)
    deps=parse((a.root/'dependencies.json').read_bytes());results=[]
    for row in deps:
        p=a.campaign_root/safe(row['directory']);_,nf,nd=inventory(p,row['manifest'],row['sha256']);results.append(dict(directory=row['directory'],payloads=nf,directories=nd))
    print(json.dumps(dict(result='PASS_INTEGRITY_ONLY',verdict=m['verdict'],payloads=n,directories=d,dependencies=results,writes=0,mathematics_rerun=False),sort_keys=True))
if __name__=='__main__':
    try:main()
    except (ValueError,KeyError,TypeError,OSError) as e:print('INTEGRITY_REJECT:',e);raise SystemExit(1)
