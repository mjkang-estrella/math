"""Read-only exact-selection/mode verification. Artifact checks, not mathematical gates."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, os, stat

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def check_tree(root, files, directories, root_mode='0555'):
    root=Path(root)
    assert not root.is_symlink() and root.is_dir(), 'packet root'
    assert f'{stat.S_IMODE(root.stat().st_mode):04o}'==root_mode, 'root mode'
    expected={f['path']:f for f in files}
    assert len(expected)==len(files), 'duplicate selection'
    for name in [*expected,*directories]:
        q=PurePosixPath(name)
        assert not q.is_absolute() and '..' not in q.parts and q.as_posix()==name, 'unsafe selection'
    actual_files=set();actual_dirs=set()
    for base,ds,fs in os.walk(root,followlinks=False):
        for name in ds+fs:
            p=Path(base)/name; assert not p.is_symlink(), 'symlink'
            rel=p.relative_to(root).as_posix()
            if p.is_dir():actual_dirs.add(rel)
            else:
                assert p.is_file(), 'nonregular file';actual_files.add(rel)
    assert actual_files==set(expected), 'exact file selection'
    assert actual_dirs==set(directories), 'exact directory selection'
    for name,mode in directories.items():
        assert f'{stat.S_IMODE((root/name).stat().st_mode):04o}'==mode, 'directory mode'
    for name,rec in expected.items():
        p=root/name
        assert f'{stat.S_IMODE(p.stat().st_mode):04o}'==rec['mode'], 'file mode'
        assert p.stat().st_size==rec['bytes'], 'file length'
        assert sha(p)==rec['sha256'], 'file hash'
    return len(expected)

def main():
    a=argparse.ArgumentParser()
    for k in ['packet','manifest','manifest-sha256','final','final-sha256','report','report-sha256']:
        a.add_argument('--'+k,required=True)
    x=a.parse_args()
    for p,h in [(x.manifest,x.manifest_sha256),(x.final,x.final_sha256),(x.report,x.report_sha256)]:
        assert len(h)==64 and sha(p)==h, 'detached anchor mismatch'
        assert stat.S_IMODE(Path(p).stat().st_mode)==0o444, 'detached document mode'
    m=json.loads(Path(x.manifest).read_bytes());f=json.loads(Path(x.final).read_bytes())
    assert f['manifest_sha256']==x.manifest_sha256, 'final manifest binding'
    assert f['disposition']=='PREFREEZE/no nominee', 'disposition binding'
    n=check_tree(x.packet,m['files'],m['directories'],m['root_mode'])
    print(json.dumps({'artifact_verification':'exact bytes, selection, modes, detached anchors verified','selected_files':n,'mathematical_grade':None,'writes':0}))
if __name__=='__main__':main()
