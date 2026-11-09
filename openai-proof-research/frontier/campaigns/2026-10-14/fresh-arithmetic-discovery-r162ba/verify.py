"""Read-only packet verifier. Supply three DETACHED SHA256 anchors in order:
python verify.py FINAL_SHA256 MANIFEST_SHA256 REPORT_SHA256
No outside-packet files, subprocesses, network or writes are used.
"""
import sys
sys.dont_write_bytecode=True
import hashlib,json,re,stat
from pathlib import Path,PurePosixPath

def digest(data): return hashlib.sha256(data).hexdigest()
def safe(s):
    assert isinstance(s,str) and s and re.fullmatch(r"[A-Za-z0-9_./-]+",s)
    p=PurePosixPath(s)
    assert not p.is_absolute() and str(p)==s and all(x not in ('','.', '..') for x in p.parts)
    return s

def validate(root,anchors,override=None):
    override=override or {}
    def read(s):
        safe(s)
        return override[s] if s in override else (root/s).read_bytes()
    for s,h in zip(('private/FINAL.md','MANIFEST.json','REPORT.md'),anchors):
        assert re.fullmatch('[0-9a-f]{64}',h), 'bad detached anchor'
        assert digest(read(s))==h, 'detached anchor mismatch: '+s
    m=json.loads(read('MANIFEST.json'))
    assert m['schema']=='r162ba-packet-v1'
    files=m['files']; names=[safe(e['path']) for e in files]
    assert names==sorted(names) and len(names)==len(set(names)), 'unsafe, duplicate or unsorted membership'
    assert 'MANIFEST.json' not in names and 'REPORT.md' not in names
    dirs=m['directories']; dn=[safe(e['path']) for e in dirs]
    assert dn==sorted(dn) and len(dn)==len(set(dn))
    actual_files=[]; actual_dirs=[]
    def visit(base):
        for p in base.iterdir():
            rel=p.relative_to(root).as_posix(); safe(rel); s=p.lstat()
            assert not stat.S_ISLNK(s.st_mode), 'symlink'
            if stat.S_ISDIR(s.st_mode): actual_dirs.append(rel); visit(p)
            else:
                assert stat.S_ISREG(s.st_mode), 'special file'
                actual_files.append(rel)
    visit(root)
    assert sorted(actual_files)==sorted(names+['MANIFEST.json','REPORT.md']), 'file membership'
    assert sorted(actual_dirs)==dn, 'directory membership'
    for e in files:
        p=root/e['path']; data=read(e['path'])
        assert len(data)==e['bytes'] and digest(data)==e['sha256'], 'payload mismatch: '+e['path']
        assert stat.S_IMODE(p.lstat().st_mode)==e['mode'], 'file mode'
    for e in dirs: assert stat.S_IMODE((root/e['path']).lstat().st_mode)==e['mode'], 'directory mode'
    assert stat.S_IMODE(root.lstat().st_mode)==m['root_mode']
    for s,mode in m['detached_modes'].items(): assert stat.S_IMODE((root/s).lstat().st_mode)==mode
    for a,b in m['copy_pairs']: assert read(safe(a))==read(safe(b)), 'copied control'
    for e in json.loads(read('private/exception-copies.json')):
        data=read(e['copy'])
        assert len(data)==e['bytes'] and digest(data)==e['sha256'], 'completed exception copy'
    for e in json.loads(read('private/authentication.json')):
        data=read('private/canonical/'+safe(e['path']))
        assert len(data)==e['bytes'] and digest(data)==e['sha256']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']
    return len(files),len(dirs)

def main():
    assert len(sys.argv)==4, __doc__
    root=Path(__file__).resolve().parent; anchors=sys.argv[1:]
    counts=validate(root,anchors)
    # Tiny copied-control and detached-anchor failures, in memory only.
    for change in ({'private/control/copy.txt':b'corrupt'}, {'private/FINAL.md':b'corrupt'}):
        try: validate(root,anchors,change)
        except AssertionError: pass
        else: raise AssertionError('corruption was not rejected')
    print(json.dumps({'artifact_authentication':'passed','payload_files':counts[0],'whole_root_files':counts[0]+2,'subdirectories':counts[1],'in_memory_rejection_controls':2,'mathematical_gate':False}))
if __name__=='__main__': main()
