"""Read-only artifact verification with three explicit detached anchors."""
from pathlib import Path, PurePosixPath
import argparse,hashlib,json,sys

def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def verify(packet,manifest,report,anchors):
    for path,expected in [(packet/'FINAL.md',anchors[0]),(manifest,anchors[1]),(report,anchors[2])]:
        if digest(path)!=expected: raise ValueError('detached anchor mismatch: '+path.name)
    data=json.loads(manifest.read_text()); entries=data['files']; wanted=set()
    for e in entries:
        rel=PurePosixPath(e['path'])
        if rel.is_absolute() or '..' in rel.parts or str(rel) in wanted: raise ValueError('invalid/duplicate manifest path')
        wanted.add(str(rel)); path=packet/str(rel)
        if path.is_symlink() or not path.is_file(): raise ValueError('missing/symlink packet member: '+str(rel))
        if path.stat().st_size!=e['bytes'] or digest(path)!=e['sha256']: raise ValueError('member mismatch: '+str(rel))
    actual=set()
    for path in packet.rglob('*'):
        if path.is_symlink(): raise ValueError('symlink in packet')
        if path.is_file(): actual.add(path.relative_to(packet).as_posix())
    if actual!=wanted: raise ValueError('packet membership differs')
    return len(entries)
if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('--packet',type=Path,required=True); p.add_argument('--manifest',type=Path,required=True); p.add_argument('--report',type=Path,required=True)
    for n in ['final','manifest','report']:p.add_argument('--'+n+'-sha256',required=True)
    a=p.parse_args()
    try:
        n=verify(a.packet,a.manifest,a.report,(a.final_sha256,a.manifest_sha256,a.report_sha256)); print('MATCH:',n,'files; artifact hashes only')
    except Exception as e: print('MISMATCH:',e,file=sys.stderr); sys.exit(1)
