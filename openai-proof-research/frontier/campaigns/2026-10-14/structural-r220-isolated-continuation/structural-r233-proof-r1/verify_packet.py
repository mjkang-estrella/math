#!/usr/bin/env python3
"""Read-only exact-selection/mode verification with explicit detached anchors."""
import argparse, hashlib, json, os, re, stat
from pathlib import Path, PurePosixPath
ROOT_REL='frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/structural-r233-proof-r1'
DETACHED={'FINAL.md','MANIFEST.json','REPORT.md','ANCHORS.json','SEAL-CHECK.json'}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def regular(p):
    s=p.lstat()
    if not stat.S_ISREG(s.st_mode):raise ValueError('nonregular or symlink file')
    return s

def safe(s):
    if not isinstance(s,str) or not s or '\\' in s:raise ValueError('unsafe selected name')
    p=PurePosixPath(s)
    if p.is_absolute() or '..' in p.parts or p.as_posix()!=s or s=='.':raise ValueError('unsafe selected path')
    return s

def surface(base):
    st=base.lstat()
    if not stat.S_ISDIR(st.st_mode):raise ValueError('root not a non-symlink directory')
    out=set()
    for d,dirs,files in os.walk(base,followlinks=False):
        for n in dirs:
            if not stat.S_ISDIR((Path(d)/n).lstat().st_mode):raise ValueError('symlink/non-directory surface')
        for n in files:
            p=Path(d)/n;regular(p);out.add(p.relative_to(base).as_posix())
    return out

def verify_payload(base,entries,selected):
    names=[safe(e['path']) for e in entries];wanted=[safe(s) for s in selected]
    if names!=sorted(set(names)) or wanted!=sorted(set(wanted)) or names!=wanted:raise ValueError('exact selection mismatch')
    for e in entries:
        p=base/e['path'];s=regular(p)
        if e['mode']!='0444' or stat.S_IMODE(s.st_mode)!=0o444:raise ValueError('payload mode mismatch')
        if s.st_size!=e['bytes'] or sha(p)!=e['sha256']:raise ValueError('payload byte/hash mismatch')

def verify_surface(base,selected,detached=frozenset()):
    if surface(base)!=set(selected)|set(detached):raise ValueError('exact surface mismatch')

def verify(base,anchors):
    if set(anchors)!={'FINAL.md','MANIFEST.json','REPORT.md'}:raise ValueError('missing explicit anchors')
    for n,h in anchors.items():
        s=regular(base/n)
        if not re.fullmatch('[0-9a-f]{64}',h) or sha(base/n)!=h:raise ValueError('detached anchor mismatch')
        if stat.S_IMODE(s.st_mode)!=0o444:raise ValueError('detached anchor mode mismatch')
    m=json.loads((base/'MANIFEST.json').read_bytes());selection=json.loads((base/'selection.json').read_bytes())
    if m['root']!=ROOT_REL or selection['root']!=ROOT_REL:raise ValueError('logical root mismatch')
    sd=sha(base/'selection.json')
    if m['selection_sha256']!=sd:raise ValueError('selection hash mismatch')
    lines=(base/'FINAL.md').read_text().splitlines()
    if 'selection_sha256='+sd not in lines or 'manifest_sha256='+anchors['MANIFEST.json'] not in lines:raise ValueError('FINAL binding mismatch')
    if m['detached_outside_manifest']!=sorted(DETACHED):raise ValueError('detached selection mismatch')
    verify_payload(base,m['entries'],selection['paths'])
    verify_surface(base,selection['paths'],DETACHED)
    for n in DETACHED:
        if stat.S_IMODE(regular(base/n).st_mode)!=0o444:raise ValueError('detached mode mismatch')
    if json.loads((base/'ANCHORS.json').read_bytes())!=anchors:raise ValueError('anchor file mismatch')
    return {'artifact_verification':'exact selected bytes, modes and complete surface verified','selected_files':len(selection['paths']),'detached_files':5,'anchors':anchors,'read_only':True,'mathematical_gate':False}

def main():
    p=argparse.ArgumentParser();p.add_argument('--root',required=True)
    for n in ['final','manifest','report']:p.add_argument('--'+n+'-sha256',required=True)
    a=p.parse_args();anchors={'FINAL.md':a.final_sha256,'MANIFEST.json':a.manifest_sha256,'REPORT.md':a.report_sha256}
    print(json.dumps(verify(Path(a.root),anchors),indent=2,sort_keys=True))
if __name__=='__main__':main()
