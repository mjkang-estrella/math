#!/usr/bin/env python3
# MIT. Integrity only, not mathematical verification.
import hashlib,json,os,stat,sys
from pathlib import Path

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
    # Do not resolve root: that would hide a root symlink.
    real_directory_chain(root)
    manifest=root/'manifest.json';st=os.lstat(manifest)
    if not stat.S_ISREG(st.st_mode) or st.st_nlink!=1:raise ValueError('manifest link/nonregular')
    if len(anchor)!=64 or digest(manifest)!=anchor:raise ValueError('external anchor mismatch')
    expected=json.loads(manifest.read_text())
    if inventory(root)!=expected:raise ValueError('exact directory/file inventory mismatch')
    tree=json.loads((root/'private/context/preprints-tree.json').read_text())
    assert tree['truncated'] is False
    blobs={r['path']:r['sha']for r in tree['tree']if r['type']=='blob'}
    receipts=[]
    for name in ['source-receipts.json','267-source-receipts.json']:
        receipts.extend(json.loads((root/name).read_text()))
    for r in receipts:
        b=(root/'private'/r['path']).read_bytes()
        assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==r['git_blob']==blobs[r['path']]
        assert hashlib.sha256(b).hexdigest()==r['sha256']
    for r in json.loads((root/'private/primary/receipt.json').read_text()):
        assert digest(root/'private/primary'/(r['name']+'.pdf'))==r['sha256']
        assert digest(root/'private/primary'/(r['name']+'.txt'))==r['text_sha256']
    return len(expected['files']),len(expected['directories'])
if __name__=='__main__':
    if len(sys.argv)!=3:raise SystemExit('usage: verify.py ROOT EXTERNAL_MANIFEST_SHA256')
    try:
        n,d=verify(Path(sys.argv[1]).absolute(),sys.argv[2]);print(f'PASS_INTEGRITY_ONLY files={n} directories={d}')
    except Exception as e:raise SystemExit('REJECT: '+str(e))
