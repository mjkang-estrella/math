"""Read-only exact-tree integrity verifier. No imports from the packet, no code execution."""
import argparse,hashlib,json,os,stat
from pathlib import Path

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def verify(root,anchors):
    envelopes={'FINAL.md','MANIFEST.json','REPORT.md'}
    for name,expected in anchors.items():
        p=root/name
        assert p.is_file() and not p.is_symlink(),('envelope',name)
        assert digest(p)==expected,('detached anchor',name)
    m=json.loads((root/'MANIFEST.json').read_text())
    assert m['schema']=='r149-exact-tree-v1'
    expected=m['files'];assert not (set(expected)&envelopes)
    files={};dirs=[]
    for base,ds,fs in os.walk(root,topdown=True,followlinks=False):
        rel=Path(base).relative_to(root).as_posix();dirs.append(rel)
        for n in ds+fs:
            p=Path(base)/n;st=p.lstat()
            assert not stat.S_ISLNK(st.st_mode),('symlink',str(p))
            assert stat.S_ISDIR(st.st_mode) or stat.S_ISREG(st.st_mode),('type',str(p))
            if stat.S_ISREG(st.st_mode):assert st.st_nlink==1,('hardlink',str(p))
        for n in fs:
            p=Path(base)/n;r=p.relative_to(root).as_posix()
            if r in envelopes:continue
            files[r]={'bytes':p.stat().st_size,'sha256':digest(p)}
    assert sorted(dirs)==m['directories'],'directory membership'
    assert files==expected,'file membership, bytes or digest'
    assert anchors['MANIFEST.json'] in (root/'FINAL.md').read_text(),'FINAL binding'
    report=(root/'REPORT.md').read_text()
    assert anchors['FINAL.md'] in report and anchors['MANIFEST.json'] in report,'REPORT binding'
    return {'integrity':'verified','files':len(files),'directories':len(dirs),'mathematical_gate':False}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True)
    p.add_argument('--final-sha256',required=True);p.add_argument('--manifest-sha256',required=True);p.add_argument('--report-sha256',required=True)
    a=p.parse_args()
    try:print(json.dumps(verify(a.root,{'FINAL.md':a.final_sha256,'MANIFEST.json':a.manifest_sha256,'REPORT.md':a.report_sha256}),sort_keys=True))
    except (AssertionError,OSError,ValueError,KeyError) as e:p.exit(1,'INTEGRITY REJECT: '+str(e)+'\n')
