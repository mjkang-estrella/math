#!/usr/bin/env python3
"""MIT. Verify an externally anchored exact inventory; never reseal."""
import hashlib,json,os,stat,sys
from pathlib import Path

def sha(b):return hashlib.sha256(b).hexdigest()

def check(expected):
    root=Path(os.path.abspath(__file__)).parent
    for p in (root,*root.parents):
        if not stat.S_ISDIR(p.lstat().st_mode):raise ValueError('non-directory or symlink ancestor')
    files={};dirs=[]
    def walk(p):
        for entry in os.scandir(p):
            q=Path(entry.path); rel=q.relative_to(root).as_posix();s=q.lstat()
            if stat.S_ISDIR(s.st_mode):dirs.append(rel);walk(q)
            elif stat.S_ISREG(s.st_mode):
                if s.st_nlink!=1:raise ValueError('hardlink: '+rel)
                if q.name=='manifest.json' and rel!='manifest.json':raise ValueError('nested manifest')
                files[rel]={'bytes':s.st_size,'sha256':sha(q.read_bytes())}
            else:raise ValueError('nonregular entry: '+rel)
    walk(root)
    raw=(root/'manifest.json').read_bytes()
    if sha(raw)!=expected:raise ValueError('external manifest anchor mismatch')
    manifest=json.loads(raw)
    if sorted(dirs)!=manifest['directories']:raise ValueError('directory inventory mismatch')
    del files['manifest.json']
    if files!=manifest['files']:raise ValueError('file inventory mismatch')
    receipts=json.loads((root/'source203-receipts.json').read_text())
    inv=json.loads((root/'source-family-inventory.json').read_text())
    actual={r['source_path']:r['git_blob'] for r in receipts}
    wanted={r['path']:r['sha'] for r in inv['entries'] if r['type']=='blob' and not r['path'].lower().endswith('.pdf')}
    if actual!=wanted:raise ValueError('source completeness mismatch')
    for r in receipts:
        b=(root/r['path']).read_bytes()
        git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        if git!=r['git_blob'] or sha(b)!=r['sha256'] or len(b)!=r['bytes']:raise ValueError('source identity mismatch')
    for r in json.loads((root/'primary-receipts.json').read_text()):
        b=(root/r['path']).read_bytes()
        if sha(b)!=r['sha256'] or len(b)!=r['bytes']:raise ValueError('primary identity mismatch')
    print(json.dumps({'status':'PASS','files':len(files),'directories':len(dirs),'source_blobs':len(receipts)}))

if __name__=='__main__':
    try:
        if len(sys.argv)!=2 or len(sys.argv[1])!=64:raise ValueError('external SHA256 argument required')
        check(sys.argv[1])
    except Exception as e:
        print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
