"""Read-only artifact verification. All detached anchors are mandatory."""
from pathlib import Path
import argparse,hashlib,json,sys

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def verify(packet, manifest_sha, final_sha, report, report_sha, working=None):
    packet=Path(packet).resolve(); report=Path(report).resolve()
    if sha(packet/'MANIFEST.json')!=manifest_sha: raise ValueError('manifest anchor mismatch')
    if sha(packet/'FINAL.md')!=final_sha: raise ValueError('FINAL anchor mismatch')
    if sha(report)!=report_sha: raise ValueError('REPORT anchor mismatch')
    manifest=json.loads((packet/'MANIFEST.json').read_bytes())
    members=manifest['members']; names=[m['path'] for m in members]
    if len(names)!=len(set(names)): raise ValueError('duplicate member')
    actual={p.relative_to(packet).as_posix() for p in packet.rglob('*') if p.is_file()}
    if any(p.is_symlink() for p in packet.rglob('*')): raise ValueError('symlink in packet')
    if actual!=set(names)|{'MANIFEST.json'}: raise ValueError('exact membership mismatch')
    for m in members:
        rel=Path(m['path'])
        if rel.is_absolute() or '..' in rel.parts: raise ValueError('unsafe member path')
        p=packet/rel
        if p.stat().st_size!=m['bytes'] or sha(p)!=m['sha256']: raise ValueError('member bytes mismatch: '+str(rel))
        if p.stat().st_mode&0o777!=m['mode']: raise ValueError('member mode mismatch: '+str(rel))
        if working:
            w=Path(working)/rel
            if not w.is_file() or w.stat().st_size!=m['bytes'] or sha(w)!=m['sha256'] or w.stat().st_mode&0o777!=m['mode']:
                raise ValueError('working counterpart mismatch: '+str(rel))
    return len(members)

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    for flag in ['packet','manifest-sha256','final-sha256','report','report-sha256']: ap.add_argument('--'+flag,required=True)
    ap.add_argument('--working')
    a=ap.parse_args()
    try:
        n=verify(a.packet,a.manifest_sha256,a.final_sha256,a.report,a.report_sha256,a.working)
        print(json.dumps({'artifact_check':'matched','members':n,'working_compared':bool(a.working)}))
    except Exception as e:
        print(str(e),file=sys.stderr);sys.exit(1)
