"""Read-only exact-membership verifier. MIT. Requires three detached anchors."""
import argparse,hashlib,json,os,re,stat
from pathlib import Path
ENV=('FINAL.md','MANIFEST.json','REPORT.md')
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def inventory(root):
    assert root.is_dir() and not root.is_symlink(),'bad root'
    files={};dirs=['.']
    for base,ds,fs in os.walk(root,topdown=True,followlinks=False):
        for name in ds+fs:
            q=Path(base)/name;s=q.lstat();rel=q.relative_to(root).as_posix()
            assert not stat.S_ISLNK(s.st_mode),'symlink: '+rel
            if stat.S_ISDIR(s.st_mode):dirs.append(rel)
            else:
                assert stat.S_ISREG(s.st_mode) and s.st_nlink==1,'nonregular/hardlinked: '+rel
                files[rel]={'size':s.st_size,'sha256':digest(q)}
    return files,sorted(dirs)
def verify(root,anchors):
    for name,h in zip(ENV,anchors):
        assert re.fullmatch('[0-9a-f]{64}',h),'malformed anchor'
        assert digest(root/name)==h,'detached anchor mismatch: '+name
    m=json.loads((root/'MANIFEST.json').read_text())
    files,dirs=inventory(root)
    for name in ENV:files.pop(name)
    assert m['schema']=='r151-exact-payload-v1'
    assert files==m['files'],'payload membership/bytes mismatch'
    assert dirs==m['directories'],'directory membership mismatch'
    return {'verified_payloads':len(files),'whole_root_files':len(files)+3,'directories':len(dirs)}
if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('root',type=Path)
    for name in ('final','manifest','report'):a.add_argument('--'+name,required=True)
    x=a.parse_args()
    try:print(json.dumps(verify(x.root,(x.final,x.manifest,x.report)),sort_keys=True))
    except Exception as e:print(type(e).__name__+': '+str(e));raise SystemExit(1)
