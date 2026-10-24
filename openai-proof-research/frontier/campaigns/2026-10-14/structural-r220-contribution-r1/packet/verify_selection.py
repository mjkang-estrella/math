#!/usr/bin/env python3
"""Read-only verifier of this review's own exact selection; detached anchors required."""
from pathlib import Path
import argparse, hashlib, json, os, stat

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def mode(p):
    return format(stat.S_IMODE(Path(p).lstat().st_mode), '04o')

def inventory(packet):
    packet=Path(packet)
    files=[]; directories=[]
    if packet.is_symlink() or not packet.is_dir(): raise ValueError('invalid packet directory')
    for base, ds, fs in os.walk(packet, followlinks=False):
        p=Path(base)
        if p.is_symlink(): raise ValueError('symlink directory')
        directories.append({'path':p.relative_to(packet).as_posix(),'mode':mode(p)})
        for n in ds:
            if (p/n).is_symlink(): raise ValueError('symlink directory')
        for n in fs:
            f=p/n
            if not stat.S_ISREG(f.lstat().st_mode): raise ValueError('nonregular member')
            b=f.read_bytes()
            files.append({'path':f.relative_to(packet).as_posix(),'bytes':len(b),'mode':mode(f),'sha256':hashlib.sha256(b).hexdigest()})
    return sorted(files,key=lambda e:e['path']),sorted(directories,key=lambda e:e['path'])

def verify(root, manifest_sha, final_sha, report_sha):
    root=Path(root)
    for h in (manifest_sha,final_sha,report_sha):
        if len(h)!=64 or any(c not in '0123456789abcdef' for c in h):raise ValueError('invalid explicit anchor')
    if root.is_symlink() or not root.is_dir():raise ValueError('invalid review root')
    for n,h in [('MANIFEST.json',manifest_sha),('REPORT.md',report_sha)]:
        p=root/n
        if not stat.S_ISREG(p.lstat().st_mode) or sha(p)!=h:raise ValueError(n+' detached anchor mismatch')
    m=json.loads((root/'MANIFEST.json').read_bytes())
    if m['format']!='structural220-contribution-r1-exact-selection-v1':raise ValueError('wrong manifest schema')
    for n,expected in m['outside_modes'].items():
        p=root if n=='.' else root/n
        if p.is_symlink() or mode(p)!=expected:raise ValueError('outside mode mismatch')
    for entries in (m['files'],m['directories']):
        names=[e['path'] for e in entries]
        if len(names)!=len(set(names)):raise ValueError('duplicate member')
        for n in names:
            p=Path(n)
            if p.is_absolute() or '..' in p.parts or p.as_posix()!=n:raise ValueError('noncanonical member')
    fs,ds=inventory(root/'packet')
    if fs!=m['files'] or ds!=m['directories']:raise ValueError('exact selection/bytes/modes mismatch')
    if sha(root/'packet/FINAL.md')!=final_sha:raise ValueError('FINAL detached anchor mismatch')
    return {'artifact_verification':'PASS: this review selection only','files':len(fs),'directories':len(ds),
            'manifest_sha256':manifest_sha,'final_sha256':final_sha,'report_sha256':report_sha,
            'mathematical_gate':'none','correctness_condition':'UNDISCHARGED in contribution role'}

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--root',required=True)
    p.add_argument('--manifest-sha256',required=True)
    p.add_argument('--final-sha256',required=True)
    p.add_argument('--report-sha256',required=True)
    a=p.parse_args()
    print(json.dumps(verify(a.root,a.manifest_sha256,a.final_sha256,a.report_sha256),indent=2))
