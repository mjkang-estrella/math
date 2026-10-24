"""Read-only verifier. Explicit detached anchors are mandatory; no anchor autodiscovery."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, os, stat, sys

def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()

def verify(packet, report, final_anchor, manifest_anchor, report_anchor):
    for value in (final_anchor,manifest_anchor,report_anchor):
        if len(value)!=64 or any(x not in '0123456789abcdef' for x in value):raise ValueError('invalid explicit anchor')
    if packet.is_symlink() or report.is_symlink():raise ValueError('symlink endpoint')
    mpath=packet/'MANIFEST.json'
    if sha(mpath)!=manifest_anchor:raise ValueError('MANIFEST anchor mismatch')
    if sha(packet/'FINAL.md')!=final_anchor:raise ValueError('FINAL anchor mismatch')
    if sha(report)!=report_anchor:raise ValueError('REPORT anchor mismatch')
    if stat.S_IMODE(report.stat().st_mode)!=0o444:raise ValueError('REPORT mode mismatch')
    m=json.loads(mpath.read_bytes())
    if m['format']!='r213-exact-packet-v1':raise ValueError('wrong packet format')
    expected={x['path']:x for x in m['files']}
    if len(expected)!=len(m['files']) or 'MANIFEST.json' in expected:raise ValueError('duplicate or self-listed path')
    for p in expected:
        q=PurePosixPath(p)
        if q.is_absolute() or '..' in q.parts or str(q)!=p:raise ValueError('unsafe path')
    files=set();dirs=set()
    def walk(p):
        rel=p.relative_to(packet).as_posix();dirs.add(rel)
        if stat.S_IMODE(p.stat().st_mode)!=0o555:raise ValueError('directory mode mismatch: '+rel)
        with os.scandir(p) as it:
            for e in it:
                child=Path(e.path)
                if e.is_symlink():raise ValueError('symlink: '+str(child))
                if e.is_dir(follow_symlinks=False):walk(child)
                elif e.is_file(follow_symlinks=False):files.add(child.relative_to(packet).as_posix())
                else:raise ValueError('non-regular artifact')
    walk(packet)
    if files!=set(expected)|{'MANIFEST.json'}:raise ValueError('exact file selection mismatch')
    if dirs!=set(m['directories']):raise ValueError('exact directory selection mismatch')
    if stat.S_IMODE(mpath.stat().st_mode)!=0o444:raise ValueError('MANIFEST mode mismatch')
    for rel,item in expected.items():
        p=packet/rel
        if p.stat().st_size!=item['bytes']:raise ValueError('size mismatch: '+rel)
        if stat.S_IMODE(p.stat().st_mode)!=int(item['mode'],8):raise ValueError('file mode mismatch: '+rel)
        if sha(p)!=item['sha256']:raise ValueError('digest mismatch: '+rel)
    return {'artifact_verification':'PASS','files':len(expected),'directories':len(dirs),'explicit_anchors':{'FINAL':final_anchor,'MANIFEST':manifest_anchor,'REPORT':report_anchor},'writes_performed_by_verifier':0,'mathematical_gate':False}

if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--packet',required=True);a.add_argument('--report',required=True)
    a.add_argument('--final-sha256',required=True);a.add_argument('--manifest-sha256',required=True);a.add_argument('--report-sha256',required=True)
    x=a.parse_args()
    try:print(json.dumps(verify(Path(x.packet),Path(x.report),x.final_sha256,x.manifest_sha256,x.report_sha256),sort_keys=True))
    except Exception as exc:print(json.dumps({'artifact_verification':'FAIL','reason':str(exc),'mathematical_gate':False}),file=sys.stderr);sys.exit(1)
