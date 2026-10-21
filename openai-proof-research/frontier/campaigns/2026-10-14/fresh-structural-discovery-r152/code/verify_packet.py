# Original code, MIT. Read-only verifier; requires three externally supplied anchors.
import argparse,hashlib,json,os,stat
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def inventory(root):
    files={};dirs=['.']
    def visit(p):
        for e in sorted(os.scandir(p),key=lambda e:e.name):
            q=Path(e.path); rel=q.relative_to(root).as_posix();s=e.stat(follow_symlinks=False)
            if stat.S_ISLNK(s.st_mode):raise ValueError('symlink: '+rel)
            if stat.S_ISDIR(s.st_mode):dirs.append(rel);visit(q)
            elif stat.S_ISREG(s.st_mode):
                if s.st_nlink!=1:raise ValueError('hardlink: '+rel)
                files[rel]={'size':s.st_size,'sha256':sha(q)}
            else:raise ValueError('nonregular: '+rel)
    if root.is_symlink() or not root.is_dir():raise ValueError('invalid root')
    visit(root)
    return files,sorted(dirs)
def verify(root,anchors):
    for name,digest in anchors.items():
        if len(digest)!=64 or any(c not in '0123456789abcdef' for c in digest):raise ValueError('invalid anchor '+name)
        if sha(root/name)!=digest:raise ValueError('detached anchor mismatch: '+name)
    m=json.loads((root/'MANIFEST.json').read_text())
    if m.get('schema')!='r152-exact-payload-v1':raise ValueError('schema')
    files,dirs=inventory(root)
    if set(files)!=set(m['files'])|set(anchors):raise ValueError('file membership')
    if dirs!=m['directories']:raise ValueError('directory membership')
    for p,entry in m['files'].items():
        if files[p]!=entry:raise ValueError('payload mismatch: '+p)
    return {'artifact_integrity':'matched','payload_files':len(m['files']),'outside_envelopes':3,'directories':len(dirs),'mathematical_gate':False}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('root',type=Path)
    p.add_argument('--final-sha256',required=True);p.add_argument('--manifest-sha256',required=True);p.add_argument('--report-sha256',required=True)
    a=p.parse_args()
    try:result=verify(a.root,{'FINAL.md':a.final_sha256,'MANIFEST.json':a.manifest_sha256,'REPORT.md':a.report_sha256})
    except (OSError,ValueError,KeyError,TypeError) as exc:raise SystemExit('REJECT: '+str(exc))
    print(json.dumps(result,sort_keys=True))
