"""Read-only exact-membership verifier. Three detached anchors are mandatory.
Run: python -B code/verify.py ROOT --final HASH --manifest HASH --report HASH
This checks artifacts, not mathematics. Never import or execute payload code.
"""
import argparse,hashlib,json,os,stat
from pathlib import Path
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def inventory(root):
    root=Path(root)
    if root.is_symlink() or not root.is_dir():raise ValueError('root must be an ordinary directory')
    files={};dirs={'.':stat.S_IMODE(root.stat().st_mode)}
    for base,ds,fs in os.walk(root,followlinks=False):
        ds.sort();fs.sort()
        for name in ds:
            p=Path(base)/name
            if p.is_symlink() or not p.is_dir():raise ValueError('non-directory/symlink '+str(p))
            dirs[p.relative_to(root).as_posix()]=stat.S_IMODE(p.stat().st_mode)
        for name in fs:
            p=Path(base)/name;s=p.lstat()
            if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1:raise ValueError('nonregular/link '+str(p))
            rel=p.relative_to(root).as_posix()
            if rel in ENVELOPES:continue
            files[rel]={'bytes':s.st_size,'sha256':digest(p),'mode':stat.S_IMODE(s.st_mode)}
    return {'schema':'r148-exact-payload-v1','excluded_root_envelopes':sorted(ENVELOPES),'directories':dirs,'files':files}
def verify(root,anchors):
    root=Path(root)
    if set(anchors)!=ENVELOPES:raise ValueError('exactly three detached anchors required')
    for name,expected in anchors.items():
        if len(expected)!=64 or any(c not in '0123456789abcdef' for c in expected):raise ValueError('invalid detached hash')
        p=root/name
        if p.is_symlink() or not p.is_file() or p.stat().st_nlink!=1:raise ValueError('unsafe envelope '+name)
        if digest(p)!=expected:raise ValueError('detached anchor mismatch '+name)
    declared=json.loads((root/'MANIFEST.json').read_text())
    actual=inventory(root)
    if declared!=actual:raise ValueError('exact payload membership/content/mode mismatch')
    return {'artifact_verification':'matched','payload_files':len(actual['files']),'directories_including_root':len(actual['directories']),'mathematical_gate':False}
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('root');p.add_argument('--final',required=True);p.add_argument('--manifest',required=True);p.add_argument('--report',required=True);a=p.parse_args()
    try:result=verify(a.root,{'FINAL.md':a.final,'MANIFEST.json':a.manifest,'REPORT.md':a.report})
    except Exception as e:print(json.dumps({'artifact_verification':'rejected','reason':str(e)}));return 1
    print(json.dumps(result));return 0
if __name__=='__main__':raise SystemExit(main())
