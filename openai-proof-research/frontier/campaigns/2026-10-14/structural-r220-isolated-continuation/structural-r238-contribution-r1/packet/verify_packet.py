"""Read-only exact selection/hash/mode verifier. Explicit detached anchors required."""
from pathlib import Path
import argparse, hashlib, json, stat

p=argparse.ArgumentParser()
for n in ['packet','manifest-sha256','final-sha256','report','report-sha256']:
    p.add_argument('--'+n,required=True)
a=p.parse_args()
root=Path(a.packet)
report=Path(a.report)
def sha(b): return hashlib.sha256(b).hexdigest()
def mode(p): return format(stat.S_IMODE(p.lstat().st_mode),'04o')
def require(c,m):
    if not c: raise SystemExit('FAIL: '+m)
def safe(rel):
    q=Path(rel)
    require(not q.is_absolute() and '..' not in q.parts,'unsafe manifest path')
    return root/q
require(root.is_dir() and not root.is_symlink(),'packet directory')
manifest=root/'MANIFEST.json'
require(manifest.is_file() and not manifest.is_symlink(),'manifest file')
mb=manifest.read_bytes()
require(sha(mb)==a.manifest_sha256,'detached manifest hash')
require(mode(manifest)=='0444','manifest mode')
m=json.loads(mb)
files=m['files']; dirs=m['directories']
require(len({x['path'] for x in files})==len(files),'duplicate file selection')
require(len({x['path'] for x in dirs})==len(dirs),'duplicate directory selection')
actual_files=set();actual_dirs={'.'}
for q in root.rglob('*'):
    require(not q.is_symlink(),'symlink in packet')
    rel=q.relative_to(root).as_posix()
    if q.is_file():actual_files.add(rel)
    elif q.is_dir():actual_dirs.add(rel)
    else:require(False,'special file in packet')
require(actual_files=={x['path'] for x in files}|{'MANIFEST.json'},'exact file selection')
require(actual_dirs=={x['path'] for x in dirs},'exact directory selection')
for x in files:
    q=safe(x['path']);b=q.read_bytes()
    require(len(b)==x['bytes'] and sha(b)==x['sha256'],'selected identity '+x['path'])
    require(mode(q)==x['mode'],'selected file mode '+x['path'])
for x in dirs:
    require(mode(safe(x['path']))==x['mode'],'directory mode '+x['path'])
require(sha((root/'FINAL.md').read_bytes())==a.final_sha256,'detached final hash')
require(report.is_file() and not report.is_symlink(),'outside report file')
require(sha(report.read_bytes())==a.report_sha256,'detached report hash')
require(mode(report)=='0444','outside report mode')
print(json.dumps({'verified':True,'selected_files':len(files),'directories':len(dirs),
                  'read_only':True,'manifest_sha256':a.manifest_sha256,
                  'final_sha256':a.final_sha256,'report_sha256':a.report_sha256}))
