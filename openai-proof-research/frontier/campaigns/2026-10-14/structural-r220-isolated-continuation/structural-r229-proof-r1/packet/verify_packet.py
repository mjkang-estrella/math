"""Read-only verifier for this review's exact selected packet and detached anchors.
Run with python3 -I -B; every anchor is required explicitly. No file writes.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import stat
import sys

parser=argparse.ArgumentParser()
for name in ['packet','manifest-sha256','final-sha256','report','report-sha256']:
    parser.add_argument('--'+name,required=True)
a=parser.parse_args()

def need(ok,message):
    if not ok: raise ValueError(message)
def sha(b): return hashlib.sha256(b).hexdigest()
def regular(path):
    need(stat.S_ISREG(path.lstat().st_mode),'not regular: '+str(path))
def mode(path): return format(stat.S_IMODE(path.lstat().st_mode),'04o')
def inventory(root):
    out={}
    def descend(d):
        for p in sorted(d.iterdir(),key=lambda x:x.name):
            s=p.lstat();rel=p.relative_to(root).as_posix()
            need(not stat.S_ISLNK(s.st_mode),'symlink: '+rel)
            need(stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode),'unsupported type: '+rel)
            if rel=='MANIFEST.json': continue
            out[rel]=p
            if stat.S_ISDIR(s.st_mode): descend(p)
    descend(root)
    return out

try:
    root=Path(a.packet);report=Path(a.report)
    need(stat.S_ISDIR(root.lstat().st_mode),'packet root type')
    manifest=root/'MANIFEST.json';final=root/'FINAL.md'
    for p,h in [(manifest,a.manifest_sha256),(final,a.final_sha256),(report,a.report_sha256)]:
        need(len(h)==64 and all(c in '0123456789abcdef' for c in h),'anchor syntax')
        regular(p);need(sha(p.read_bytes())==h,'detached anchor mismatch: '+p.name)
    data=json.loads(manifest.read_bytes())
    need(data['format']=='structural229-correctness-r1-exact-v1','format')
    need(mode(root)==data['root_mode']=='0500','root mode')
    need(mode(manifest)=='0400','manifest mode')
    need(mode(report)=='0444','outside report mode')
    entries=data['entries'];names=[e['path'] for e in entries]
    need(len(names)==len(set(names)),'duplicate selected path')
    need(len(names)==len({n.casefold() for n in names}),'casefold collision')
    need('FINAL.md' in names and 'MANIFEST.json' not in names,'manifest/final selection')
    for n in names:
        p=PurePosixPath(n)
        need(n==p.as_posix() and not p.is_absolute() and '..' not in p.parts and '\\' not in n,'unsafe path')
    actual=inventory(root)
    need(set(actual)==set(names),'exact selection mismatch')
    for e in entries:
        p=actual[e['path']];s=p.lstat()
        need(mode(p)==e['mode'],'mode mismatch: '+e['path'])
        if e['type']=='directory':
            need(stat.S_ISDIR(s.st_mode),'directory type: '+e['path'])
        else:
            need(e['type']=='file' and stat.S_ISREG(s.st_mode),'file type: '+e['path'])
            b=p.read_bytes()
            need(len(b)==e['bytes'],'size mismatch: '+e['path'])
            need(sha(b)==e['sha256'],'content mismatch: '+e['path'])
    print(json.dumps({'artifact_only':True,'result':'exact selection, explicit detached anchors, bytes and modes agree',
                      'files':sum(e['type']=='file' for e in entries),
                      'directories':sum(e['type']=='directory' for e in entries)}))
except Exception as exc:
    print('ARTIFACT REJECTION: '+str(exc),file=sys.stderr)
    sys.exit(1)
