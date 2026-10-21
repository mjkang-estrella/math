"""Read-only exact packet verification, with three explicit detached anchors."""
from pathlib import Path
import argparse,hashlib,json,os,stat
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def inventory(root):
    files=[];dirs=[]
    for d,ds,fs in os.walk(root,topdown=True,followlinks=False):
        p=Path(d);s=p.lstat()
        assert stat.S_ISDIR(s.st_mode) and not p.is_symlink(),str(p)
        dirs.append({'path':'.' if p==root else p.relative_to(root).as_posix(),'mode':stat.S_IMODE(s.st_mode)})
        for n in ds:
            q=p/n;assert not q.is_symlink(),str(q)
        for n in fs:
            q=p/n;s=q.lstat();rel=q.relative_to(root).as_posix()
            assert stat.S_ISREG(s.st_mode) and s.st_nlink==1,str(q)
            if p==root and n in ENVELOPES:continue
            files.append({'path':rel,'size':s.st_size,'mode':stat.S_IMODE(s.st_mode),'sha256':digest(q)})
    return {'files':sorted(files,key=lambda x:x['path']),'directories':sorted(dirs,key=lambda x:x['path'])}
def verify(root,anchors):
    root=Path(root).absolute();assert not root.is_symlink()
    for n,h in anchors.items():
        p=root/n;s=p.lstat();assert stat.S_ISREG(s.st_mode) and s.st_nlink==1,n
        assert len(h)==64 and digest(p)==h,'detached anchor '+n
    actual=inventory(root);expected=json.loads((root/'MANIFEST.json').read_text())
    assert expected['schema']=='r168-exact-payload-v1'
    assert actual==expected['payload'],'payload membership/bytes/modes'
    return {'files':len(actual['files']),'directories':len(actual['directories']),'verified':'bytes and membership only'}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('root');p.add_argument('--final',required=True);p.add_argument('--manifest',required=True);p.add_argument('--report',required=True);a=p.parse_args()
    print(json.dumps(verify(a.root,{'FINAL.md':a.final,'MANIFEST.json':a.manifest,'REPORT.md':a.report}),sort_keys=True))
