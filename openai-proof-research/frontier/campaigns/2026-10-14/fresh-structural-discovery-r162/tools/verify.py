"""Read-only exact packet verification. Anchors must come from outside packet."""
import argparse, hashlib, json, stat
from pathlib import Path

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def verify(root, anchors):
    root=Path(root)
    for name, anchor in anchors.items():
        assert len(anchor)==64 and digest(root/name)==anchor, f'detached anchor mismatch: {name}'
    manifest=json.loads((root/'MANIFEST.json').read_text())
    assert manifest['envelopes']==['FINAL.md','MANIFEST.json','REPORT.md'], 'envelope specification'
    files={}; dirs={}
    for p in root.rglob('*'):
        assert not p.is_symlink(), f'symlink: {p}'
        rel=p.relative_to(root).as_posix()
        mode=oct(stat.S_IMODE(p.stat().st_mode))
        if p.is_dir(): dirs[rel]=mode
        elif p.is_file() and rel not in manifest['envelopes']:
            files[rel]={'size':p.stat().st_size,'sha256':digest(p),'mode':mode}
        elif not p.is_file():raise AssertionError(f'unsupported entry: {rel}')
    assert files==manifest['files'], 'exact file membership/bytes/mode mismatch'
    assert dirs==manifest['directories'], 'exact directory membership/mode mismatch'
    return len(files),len(dirs)

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('root');parser.add_argument('--final-sha',required=True)
    parser.add_argument('--manifest-sha',required=True);parser.add_argument('--report-sha',required=True)
    a=parser.parse_args()
    n,d=verify(a.root,{'FINAL.md':a.final_sha,'MANIFEST.json':a.manifest_sha,'REPORT.md':a.report_sha})
    print(f'Artifact integrity only: {n} payloads, {d} directories, three detached anchors match.')
