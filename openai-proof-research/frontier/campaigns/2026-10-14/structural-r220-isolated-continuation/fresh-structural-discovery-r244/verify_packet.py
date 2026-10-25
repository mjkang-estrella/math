#!/usr/bin/env python3
"""Read-only exact-selection/mode checker. All three detached anchors are mandatory."""
import argparse,hashlib,json,os,stat
from pathlib import Path,PurePosixPath

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def verify(packet,manifest,report,fa,ma,ra):
    errors=[]
    for p,anchor,label in [(manifest,ma,'MANIFEST'),(report,ra,'REPORT'),(packet/'FINAL.md',fa,'FINAL')]:
        if not p.is_file() or p.is_symlink() or sha(p)!=anchor:errors.append(label+' anchor mismatch')
    if errors:return errors
    data=json.loads(manifest.read_bytes());expected={}
    for entry in data['files']:
        name=entry['path'];q=PurePosixPath(name)
        if q.is_absolute() or '..' in q.parts or str(q)!=name or name in expected:errors.append('invalid/duplicate selected path');continue
        expected[name]=entry
    observed={};dirs={}
    for base,ds,fs in os.walk(packet,followlinks=False):
        b=Path(base);rel=b.relative_to(packet).as_posix();dirs[rel]=format(stat.S_IMODE(b.lstat().st_mode),'04o')
        for n in ds:
            if (b/n).is_symlink():errors.append('directory symlink: '+(b/n).relative_to(packet).as_posix())
        for n in fs:
            p=b/n;name=p.relative_to(packet).as_posix();st=p.lstat()
            if not stat.S_ISREG(st.st_mode):errors.append('not regular: '+name);continue
            observed[name]={'path':name,'bytes':st.st_size,'mode':format(stat.S_IMODE(st.st_mode),'04o'),'sha256':sha(p)}
    if set(observed)!=set(expected):errors.append('file selection mismatch')
    for name in set(observed)&set(expected):
        if observed[name]!=expected[name]:errors.append('bytes/hash/mode mismatch: '+name)
    if dirs!=data['directories']:errors.append('directory selection/mode mismatch')
    return errors

def main():
    p=argparse.ArgumentParser();p.add_argument('--packet',required=True,type=Path);p.add_argument('--manifest',required=True,type=Path);p.add_argument('--report',required=True,type=Path);p.add_argument('--final-sha256',required=True);p.add_argument('--manifest-sha256',required=True);p.add_argument('--report-sha256',required=True);a=p.parse_args()
    try:errors=verify(a.packet,a.manifest,a.report,a.final_sha256,a.manifest_sha256,a.report_sha256)
    except Exception as e:errors=[type(e).__name__+': '+str(e)]
    print(json.dumps({'artifact_integrity_only':True,'ok':not errors,'errors':errors},sort_keys=True));return bool(errors)
if __name__=='__main__':raise SystemExit(main())
