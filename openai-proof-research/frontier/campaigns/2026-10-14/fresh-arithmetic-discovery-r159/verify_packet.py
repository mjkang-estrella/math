#!/usr/bin/env python3
"""Read-only artifact verifier. Requires independently supplied detached anchors."""
import argparse, hashlib, json, os, re, stat
from pathlib import Path, PurePosixPath

def digest(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda:f.read(1024*1024), b''): h.update(chunk)
    return h.hexdigest()

def run():
    a=argparse.ArgumentParser(description=__doc__)
    for key in ('packet','manifest','report','final-sha256','manifest-sha256','report-sha256'):
        a.add_argument('--'+key,required=True)
    x=a.parse_args()
    for v in (x.final_sha256,x.manifest_sha256,x.report_sha256):
        if not re.fullmatch('[0-9a-f]{64}',v): raise ValueError('invalid explicit SHA256 anchor')
    packet=Path(x.packet); manifest=Path(x.manifest); report=Path(x.report)
    for f in (packet,manifest,report,packet/'FINAL.md'):
        if f.is_symlink(): raise ValueError('symlink forbidden: '+str(f))
    if not packet.is_dir(): raise ValueError('missing packet')
    if digest(manifest)!=x.manifest_sha256: raise ValueError('MANIFEST anchor mismatch')
    if digest(report)!=x.report_sha256: raise ValueError('REPORT anchor mismatch')
    if digest(packet/'FINAL.md')!=x.final_sha256: raise ValueError('FINAL anchor mismatch')
    m=json.loads(manifest.read_text(encoding='utf-8'))
    if m.get('schema')!='r159-exact-packet-v1': raise ValueError('manifest schema mismatch')
    expected={}
    for entry in m['files']:
        rel=entry['path']; p=PurePosixPath(rel)
        if p.is_absolute() or '..' in p.parts or str(p)!=rel or not p.parts or '\\' in rel:
            raise ValueError('unsafe manifest path')
        if rel in expected: raise ValueError('duplicate manifest path')
        expected[rel]=entry
    actual={}
    for base,dirs,files in os.walk(packet,followlinks=False):
        for name in dirs:
            if (Path(base)/name).is_symlink(): raise ValueError('symlink directory')
        for name in files:
            f=Path(base)/name; st=f.lstat()
            if not stat.S_ISREG(st.st_mode): raise ValueError('nonregular packet object')
            rel=f.relative_to(packet).as_posix()
            actual[rel]={'path':rel,'bytes':st.st_size,'mode':stat.S_IMODE(st.st_mode),'sha256':digest(f)}
    if set(actual)!=set(expected): raise ValueError('packet file-set mismatch')
    for rel,entry in actual.items():
        if entry!=expected[rel]: raise ValueError('packet entry mismatch: '+rel)
    print(json.dumps({'artifact_integrity':'matches explicit detached anchors','files':len(actual),'bytes':sum(e['bytes'] for e in actual.values()),'mathematical_gate':False},sort_keys=True))

if __name__=='__main__':
    try: run()
    except Exception as e:
        print(json.dumps({'artifact_integrity':'rejected','error':str(e)})); raise SystemExit(1)
