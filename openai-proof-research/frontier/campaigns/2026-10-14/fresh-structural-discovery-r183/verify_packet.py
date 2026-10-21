#!/usr/bin/env python3
"""Read-only exact-packet verifier. Anchors must be supplied independently."""
import argparse, hashlib, json, os
from pathlib import Path, PurePosixPath

def digest(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''):
            h.update(block)
    return h.hexdigest()

def require(ok,message):
    if not ok: raise ValueError(message)

def verify(packet, report, final_sha, manifest_sha, report_sha):
    packet=Path(packet).resolve(); report=Path(report).resolve()
    require(not report.is_relative_to(packet),'REPORT must be outside packet')
    for a in (final_sha,manifest_sha,report_sha):
        require(len(a)==64 and all(c in '0123456789abcdef' for c in a),'invalid explicit anchor')
    require(digest(packet/'FINAL.md')==final_sha,'FINAL anchor mismatch')
    require(digest(packet/'MANIFEST.json')==manifest_sha,'MANIFEST anchor mismatch')
    require(digest(report)==report_sha,'REPORT anchor mismatch')
    data=json.loads((packet/'MANIFEST.json').read_text())
    require(data.get('format')=='r183-exact-packet-v1','manifest format')
    rows=data['files']; expected={}; total=0
    for row in rows:
        name=row['path']; p=PurePosixPath(name)
        require(not p.is_absolute() and '..' not in p.parts and p.as_posix()==name and name not in ('','.'),'unsafe member')
        require(name!='MANIFEST.json' and name not in expected,'duplicate/self manifest member')
        expected[name]=row
    require('FINAL.md' in expected,'FINAL absent from membership')
    actual=set()
    for base,dirs,files in os.walk(packet,followlinks=False):
        for name in dirs+files:
            require(not (Path(base)/name).is_symlink(),'symlink member')
        for name in files:
            rel=(Path(base)/name).relative_to(packet).as_posix()
            if rel!='MANIFEST.json':actual.add(rel)
    require(actual==set(expected),'exact membership mismatch')
    for name,row in expected.items():
        p=packet/name
        require(p.stat().st_size==row['bytes'],'member length mismatch: '+name)
        require(digest(p)==row['sha256'],'member digest mismatch: '+name)
        total+=row['bytes']
    return {'artifact_verification':'matched explicit anchors and exact membership','files':len(expected),'member_bytes':total}

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--packet',required=True);ap.add_argument('--report',required=True)
    ap.add_argument('--final-sha',required=True);ap.add_argument('--manifest-sha',required=True);ap.add_argument('--report-sha',required=True)
    a=ap.parse_args()
    print(json.dumps(verify(a.packet,a.report,a.final_sha,a.manifest_sha,a.report_sha),indent=2))
