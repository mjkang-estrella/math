#!/usr/bin/env python3
"""Read-only verification of one exact reviewer selection; never a mathematical gate."""
import argparse
import hashlib
import json
import re
import stat
from pathlib import Path, PurePosixPath

def require(ok,message):
    if not ok:
        raise ValueError(message)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def regular(path):
    require(stat.S_ISREG(path.lstat().st_mode),'not a regular file: '+str(path))

def normalized(name):
    p=PurePosixPath(name)
    return bool(name) and not p.is_absolute() and '..' not in p.parts and str(p)==name

def verify(root,final_sha,manifest_sha,report,report_sha):
    for h in (final_sha,manifest_sha,report_sha):
        require(re.fullmatch('[0-9a-f]{64}',h) is not None,'invalid explicit anchor')
    require(stat.S_ISDIR(root.lstat().st_mode),'root is not an ordinary directory')
    for name,h in [('FINAL.md',final_sha),('MANIFEST.json',manifest_sha)]:
        p=root/name; regular(p)
        require(digest(p)==h,name+' anchor mismatch')
        require(stat.S_IMODE(p.stat().st_mode)==0o400,name+' mode mismatch')
    regular(report)
    require(digest(report)==report_sha,'REPORT anchor mismatch')
    require(stat.S_IMODE(report.stat().st_mode)==0o400,'REPORT mode mismatch')
    m=json.loads((root/'MANIFEST.json').read_bytes())
    expected={'FINAL.md','MANIFEST.json'}
    for e in m['files']:
        n=e['path']; require(normalized(n) and n not in expected,'invalid or duplicate file path')
        expected.add(n)
        require(e['mode']=='0400','unexpected file mode declaration')
    dirs={'.'}
    for n in expected:
        for p in PurePosixPath(n).parents:
            dirs.add(str(p))
    require(dirs==set(m['directories']),'invalid directory selection')
    for d in sorted(dirs,key=lambda x:(len(PurePosixPath(x).parts),x)):
        require(d=='.' or normalized(d),'invalid directory path')
        p=root/d
        require(stat.S_ISDIR(p.lstat().st_mode),'directory is missing or a symlink: '+d)
        require(m['directories'][d]=='0500' and stat.S_IMODE(p.stat().st_mode)==0o500,'directory mode mismatch: '+d)
        wanted={PurePosixPath(n).name for n in expected|(dirs-{'.'}) if str(PurePosixPath(n).parent)==d}
        actual={q.name for q in p.iterdir()}
        require(actual==wanted,'exact directory membership mismatch: '+d)
    for e in m['files']:
        n=e['path']; p=root/n; regular(p)
        require(stat.S_IMODE(p.stat().st_mode)==0o400,'file mode mismatch: '+n)
        b=p.read_bytes()
        require(len(b)==e['bytes'],'file size mismatch: '+n)
        require(hashlib.sha256(b).hexdigest()==e['sha256'],'file content mismatch: '+n)
    return {'verified':True,'artifact_only':True,'explicit_anchors':True,'exact_selection':True,'modes':True,'selected_files':len(m['files']),'detached_selected_files':2,'selected_directories_including_root':len(dirs),'selected_bytes_excluding_FINAL_MANIFEST':sum(e['bytes'] for e in m['files'])}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',type=Path,required=True)
    p.add_argument('--final-sha256',required=True)
    p.add_argument('--manifest-sha256',required=True)
    p.add_argument('--report',type=Path,required=True)
    p.add_argument('--report-sha256',required=True)
    a=p.parse_args()
    try:
        print(json.dumps(verify(a.root,a.final_sha256,a.manifest_sha256,a.report,a.report_sha256),sort_keys=True))
    except Exception as e:
        print(json.dumps({'verified':False,'artifact_only':True,'error':str(e)},sort_keys=True))
        raise SystemExit(1)
