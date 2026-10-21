#!/usr/bin/env python3
"""Read-only exact-content verifier. Supply three independent detached anchors."""
import argparse, hashlib, json, os, re
from pathlib import Path

def digest(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''): h.update(b)
    return h.hexdigest()

def inventory(root):
    files={}; dirs=[]
    for base, ds, fs in os.walk(root, followlinks=False):
        for name in ds+fs:
            p=Path(base)/name
            if p.is_symlink(): raise ValueError('symlink: '+str(p))
        for name in ds: dirs.append((Path(base)/name).relative_to(root).as_posix())
        for name in fs:
            p=Path(base)/name; rel=p.relative_to(root).as_posix()
            if not p.is_file() or p.stat().st_nlink!=1: raise ValueError('nonordinary file: '+rel)
            if rel not in {'FINAL.md','MANIFEST.json','REPORT.md'}:
                files[rel]={'size':p.stat().st_size,'sha256':digest(p)}
    return {'files':dict(sorted(files.items())),'directories':sorted(dirs)}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('root',type=Path)
    for name in ['final','manifest','report']: ap.add_argument('--'+name,required=True)
    a=ap.parse_args();root=a.root
    if root.is_symlink() or not root.is_dir(): raise ValueError('invalid root')
    for name in ['final','manifest','report']:
        expected=getattr(a,name)
        if not re.fullmatch('[0-9a-f]{64}',expected): raise ValueError('invalid detached anchor')
        p=root/({'final':'FINAL.md','manifest':'MANIFEST.json','report':'REPORT.md'}[name])
        if p.is_symlink() or p.stat().st_nlink!=1 or digest(p)!=expected: raise ValueError(name+' anchor mismatch')
    expected=json.loads((root/'MANIFEST.json').read_text())
    actual=inventory(root)
    if actual!=expected['inventory']: raise ValueError('exact inventory mismatch')
    print('CONTENT CHECK OK; no mathematical verdict')

if __name__=='__main__':
    try: main()
    except Exception as exc:
        print('CONTENT CHECK FAILED:',exc)
        raise SystemExit(1)
