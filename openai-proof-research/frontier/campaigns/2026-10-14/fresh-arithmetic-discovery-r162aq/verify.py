#!/usr/bin/env python3
"""Read-only own-packet verification; anchors must come from a detached record."""
import argparse,hashlib,json
from pathlib import Path

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def within(root, relative):
    p=root/relative
    if p.is_symlink() or not p.resolve().is_relative_to(root.resolve()):
        raise ValueError('path escapes packet or is a symlink: '+relative)
    return p

def verify(root, manifest, final, report, anchors):
    root=Path(root)
    for name,rel in [('manifest',manifest),('final',final),('report',report)]:
        if sha(within(root,rel)) != anchors[name]:
            raise ValueError(name+' detached anchor mismatch')
    data=json.loads(within(root,manifest).read_text())
    records=data['files']
    if len({r['path'] for r in records}) != len(records):
        raise ValueError('duplicate manifest path')
    actual=set(data['extra_files'])
    for rel in data['coverage_roots']:
        base=within(root,rel)
        for p in base.rglob('*'):
            if p.is_symlink():raise ValueError('symlink in covered root')
            if p.is_file():actual.add(p.relative_to(root).as_posix())
    expected={r['path'] for r in records}
    if actual != expected:raise ValueError('exact covered-file selection mismatch')
    for r in records:
        p=within(root,r['path'])
        if p.stat().st_size != r['bytes'] or sha(p) != r['sha256']:
            raise ValueError('file mismatch: '+r['path'])
    return len(records)

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    for name in ['root','manifest','final','report','manifest-sha256','final-sha256','report-sha256']:
        ap.add_argument('--'+name,required=True)
    a=ap.parse_args()
    try:
        n=verify(a.root,a.manifest,a.final,a.report,dict(manifest=a.manifest_sha256,final=a.final_sha256,report=a.report_sha256))
    except (ValueError,OSError,KeyError) as e:
        ap.exit(1,'ARTIFACT CHECK FAILED: '+str(e)+'\n')
    print('ARTIFACT BYTES VERIFIED:',n,'files; no mathematical gate')
