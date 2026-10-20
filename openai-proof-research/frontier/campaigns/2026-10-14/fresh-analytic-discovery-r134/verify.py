#!/usr/bin/env python3
"""Read-only exact-packet verifier. Required anchors must come from the handoff.
This checks artifacts only, never mathematical correctness or contribution.
"""
import argparse, hashlib, json, os, stat, sys
from pathlib import Path, PurePosixPath

def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
def require(ok,msg):
    if not ok:raise ValueError(msg)
def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent)
    for n in ['manifest','final','report']:ap.add_argument('--'+n+'-sha256',required=True)
    a=ap.parse_args();r=a.root.resolve()
    anchors={'MANIFEST.json':a.manifest_sha256,'FINAL.json':a.final_sha256,'REPORT.md':a.report_sha256}
    for name,expected in anchors.items():
        p=r/name
        require(len(expected)==64 and all(c in '0123456789abcdef' for c in expected),'invalid detached anchor')
        require(p.is_file() and not p.is_symlink(),'missing/nonregular anchor file '+name)
        require(sha(p)==expected,'detached hash mismatch '+name)
    final=json.loads((r/'FINAL.json').read_text())
    require(final['manifest_sha256']==a.manifest_sha256,'FINAL manifest binding')
    require(final['outside_report_sha256']==a.report_sha256,'FINAL report binding')
    require(not (r/'verify.py').is_symlink() and sha(r/'verify.py')==final['verifier_sha256'],'verifier identity')
    manifest=json.loads((r/'MANIFEST.json').read_text()); records=manifest['files']
    names=[x['path'] for x in records]
    require(names==sorted(set(names)),'unsorted or duplicate manifest')
    for n in names:
        p=PurePosixPath(n)
        require(not p.is_absolute() and '..' not in p.parts and p.parts[0]=='packet','unsafe manifest path')
    actual=[]
    require((r/'packet').is_dir() and not (r/'packet').is_symlink(),'packet directory invalid')
    for base,ds,fs in os.walk(r/'packet',followlinks=False):
        for n in ds:
            require(stat.S_ISDIR((Path(base)/n).lstat().st_mode),'non-directory/symlink inside packet')
        for n in fs:
            p=Path(base)/n
            require(stat.S_ISREG(p.lstat().st_mode),'nonregular payload '+str(p))
            actual.append(p.relative_to(r).as_posix())
    require(sorted(actual)==names,'exact packet file set differs')
    for x in records:
        p=r/x['path']
        require(p.stat().st_size==x['bytes'],'payload size mismatch '+x['path'])
        require(sha(p)==x['sha256'],'payload hash mismatch '+x['path'])
    require(sha(r/'packet/public/FROZEN-SCOPE.md')==final['frozen_scope_sha256'],'frozen scope binding')
    print(json.dumps({'artifact_check':'PASS','files':len(records),'mathematical_gate':False}))
if __name__=='__main__':
    try:main()
    except Exception as e:
        print(json.dumps({'artifact_check':'FAIL','reason':str(e)}),file=sys.stderr)
        sys.exit(1)
