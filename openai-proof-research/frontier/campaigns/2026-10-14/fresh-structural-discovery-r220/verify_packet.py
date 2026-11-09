#!/usr/bin/env python3
"""Read-only exact-selection/mode verifier. Explicit detached anchors are mandatory."""
from pathlib import Path
import argparse, hashlib, json, os, stat

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def inspect_packet(packet):
    files=[]; directories=[]
    for root, ds, fs in os.walk(packet, followlinks=False):
        rp=Path(root)
        if rp.is_symlink(): raise ValueError('symlink directory')
        rel=rp.relative_to(packet).as_posix()
        directories.append({'path':rel,'mode':format(stat.S_IMODE(rp.stat().st_mode),'04o')})
        for name in ds:
            if (rp/name).is_symlink(): raise ValueError('symlink directory')
        for name in fs:
            p=rp/name
            if p.is_symlink() or not p.is_file(): raise ValueError('non-regular member')
            files.append({'path':p.relative_to(packet).as_posix(),'bytes':p.stat().st_size,
                          'mode':format(stat.S_IMODE(p.stat().st_mode),'04o'),'sha256':digest(p)})
    return sorted(files,key=lambda x:x['path']),sorted(directories,key=lambda x:x['path'])

def verify(root, manifest_sha, final_sha, report_sha):
    root=Path(root)
    for x in (manifest_sha, final_sha, report_sha):
        if len(x)!=64 or any(c not in '0123456789abcdef' for c in x):raise ValueError('invalid explicit anchor')
    if digest(root/'MANIFEST.json')!=manifest_sha:raise ValueError('manifest anchor mismatch')
    if digest(root/'REPORT.md')!=report_sha:raise ValueError('report anchor mismatch')
    manifest=json.loads((root/'MANIFEST.json').read_bytes())
    if manifest['format']!='r220-exact-selection-v1':raise ValueError('unsupported manifest')
    expected_files=manifest['files'];expected_dirs=manifest['directories']
    names=[x['path'] for x in expected_files]
    if len(names)!=len(set(names)):raise ValueError('duplicate member')
    for name in names:
        p=Path(name)
        if p.is_absolute() or '..' in p.parts or p.as_posix()!=name:raise ValueError('invalid member path')
    actual_files,actual_dirs=inspect_packet(root/'packet')
    if actual_files!=expected_files:raise ValueError('exact file bytes, selection, or mode mismatch')
    if actual_dirs!=expected_dirs:raise ValueError('exact directory selection or mode mismatch')
    if digest(root/'packet/FINAL.md')!=final_sha:raise ValueError('FINAL anchor mismatch')
    return {'artifact_verification':'exact selected bytes and modes matched explicit anchors',
            'files':len(actual_files),'directories':len(actual_dirs),
            'manifest_sha256':manifest_sha,'final_sha256':final_sha,'report_sha256':report_sha,
            'mathematical_review':'none; artifact checks are not mathematical gates'}

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--root',required=True)
    p.add_argument('--manifest-sha256',required=True)
    p.add_argument('--final-sha256',required=True)
    p.add_argument('--report-sha256',required=True)
    a=p.parse_args()
    print(json.dumps(verify(a.root,a.manifest_sha256,a.final_sha256,a.report_sha256),indent=2))
