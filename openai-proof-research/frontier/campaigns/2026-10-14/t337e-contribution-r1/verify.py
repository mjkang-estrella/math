#!/usr/bin/env python3
# MIT. Integrity only, not mathematical or novelty verification.
import hashlib,json,os,stat,sys
from pathlib import Path
sys.dont_write_bytecode=True

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def real_directory_chain(root):
    # Check before resolving: resolution would conceal a symlink ancestor.
    for p in (root,*root.parents):
        if not stat.S_ISDIR(os.lstat(p).st_mode):
            raise ValueError('root/ancestor link or non-directory: '+str(p))
def inventory(root):
    real_directory_chain(root)
    dirs=[];files={}
    def walk(d):
        for p in sorted(d.iterdir()):
            st=os.lstat(p);rel=p.relative_to(root).as_posix()
            if stat.S_ISDIR(st.st_mode):dirs.append(rel);walk(p)
            elif stat.S_ISREG(st.st_mode):
                if st.st_nlink!=1:raise ValueError('hardlink: '+rel)
                if rel!='manifest.json':files[rel]=digest(p)
            else:raise ValueError('link/nonregular: '+rel)
    walk(root)
    return {'directories':sorted(dirs),'files':files}

def verify(root,anchor):
    real_directory_chain(root)
    manifest=root/'manifest.json';st=os.lstat(manifest)
    if not stat.S_ISREG(st.st_mode) or st.st_nlink!=1:raise ValueError('manifest link/nonregular')
    if len(anchor)!=64 or digest(manifest)!=anchor:raise ValueError('external anchor mismatch')
    expected=json.loads(manifest.read_text())
    if inventory(root)!=expected:raise ValueError('exact directory/file inventory mismatch')
    for r in json.loads((root/'search-log.json').read_text())['web_searches_earlier_in_round']['retrieved']:
        if digest(root/r['local'])!=r['sha256']:raise ValueError('primary receipt mismatch: '+r['local'])
        if 'text_local' in r and digest(root/r['text_local'])!=r['text_sha256']:
            raise ValueError('primary receipt mismatch: '+r['text_local'])
    if json.loads((root/'author-controls-result.json').read_text())['external_anchor']!='701a9549aa13d547f101ef9dd4ff3c890274384fef4020f6d20bc8b4c7faaa20':
        raise ValueError('author packet anchor mismatch')
    return len(expected['files']),len(expected['directories'])
if __name__=='__main__':
    if len(sys.argv)!=3:raise SystemExit('usage: verify.py ROOT EXTERNAL_MANIFEST_SHA256')
    try:
        n,d=verify(Path(sys.argv[1]).absolute(),sys.argv[2]);print(f'PASS_INTEGRITY_ONLY files={n} directories={d}')
    except Exception as e:raise SystemExit('REJECT: '+str(e))
