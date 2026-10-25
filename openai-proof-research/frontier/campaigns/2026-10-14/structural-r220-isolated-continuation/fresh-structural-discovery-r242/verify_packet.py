#!/usr/bin/env python3
"""Read-only exact-selection and mode verifier; all detached anchors are mandatory."""
import argparse,hashlib,json,os,stat
from pathlib import Path
p=argparse.ArgumentParser()
p.add_argument('--root',required=True)
p.add_argument('--final-sha256',required=True)
p.add_argument('--manifest-sha256',required=True)
p.add_argument('--report-sha256',required=True)
a=p.parse_args();root=Path(a.root)
def digest(path):
    if path.is_symlink() or not path.is_file():raise ValueError('not an ordinary file: '+str(path))
    return hashlib.sha256(path.read_bytes()).hexdigest()
def demand(ok,message):
    if not ok:raise ValueError(message)
try:
    demand(digest(root/'MANIFEST.json')==a.manifest_sha256,'MANIFEST anchor mismatch')
    demand(digest(root/'REPORT.md')==a.report_sha256,'REPORT anchor mismatch')
    demand(stat.S_IMODE((root/'MANIFEST.json').stat().st_mode)==0o444,'MANIFEST mode')
    demand(stat.S_IMODE((root/'REPORT.md').stat().st_mode)==0o444,'REPORT mode')
    m=json.loads((root/'MANIFEST.json').read_bytes())
    demand(m['schema']=='r242-exact-packet-v1' and m['packet']=='packet' and m['final']=='FINAL.md','unexpected manifest schema')
    base=root/'packet';demand(not base.is_symlink(),'packet symlink')
    actual_files={};actual_dirs={'.':format(stat.S_IMODE(base.stat().st_mode),'04o')}
    for d,ds,fs in os.walk(base,followlinks=False):
        for n in ds:
            q=Path(d)/n;demand(not q.is_symlink(),'directory symlink')
            actual_dirs[q.relative_to(base).as_posix()]=format(stat.S_IMODE(q.stat().st_mode),'04o')
        for n in fs:
            q=Path(d)/n;demand(not q.is_symlink() and q.is_file(),'nonregular packet entry')
            actual_files[q.relative_to(base).as_posix()]=q
    listed={x['path']:x for x in m['files']}
    demand(len(listed)==len(m['files']),'duplicate file entry')
    demand(set(actual_files)==set(listed),'exact file selection mismatch')
    demand(actual_dirs==m['directories'],'exact directory selection or mode mismatch')
    for s,q in actual_files.items():
        row=listed[s];demand(q.stat().st_size==row['size'],'size mismatch: '+s)
        demand(format(stat.S_IMODE(q.stat().st_mode),'04o')==row['mode'],'mode mismatch: '+s)
        demand(digest(q)==row['sha256'],'content mismatch: '+s)
    demand(digest(base/'FINAL.md')==a.final_sha256,'FINAL anchor mismatch')
    print(json.dumps({'artifact_verification':'exact bytes, selection and modes matched','files':len(listed),'directories':len(actual_dirs),'mathematical_grade':None}))
except Exception as e:
    print(json.dumps({'artifact_verification':'rejected','reason':str(e)}))
    raise SystemExit(1)
