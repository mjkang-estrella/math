#!/usr/bin/env python3
"""Read-only packet verification. Supply detached anchors explicitly."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, stat, sys

def digest(b): return hashlib.sha256(b).hexdigest()
def require(ok, message):
    if not ok: raise ValueError(message)
def verify(root, final_sha, manifest_sha, report_sha):
    root=Path(root).resolve()
    for name, expected in [('FINAL.md',final_sha),('MANIFEST.json',manifest_sha),('REPORT.md',report_sha)]:
        p=root/name
        require(not p.is_symlink() and p.is_file(), 'missing/linked anchor file: '+name)
        require(len(expected)==64 and digest(p.read_bytes())==expected, 'anchor mismatch: '+name)
    manifest=json.loads((root/'MANIFEST.json').read_text())
    require(manifest['schema']=='r151-packet-v1', 'schema mismatch')
    packet=root/'packet'; require(packet.is_dir() and not packet.is_symlink(),'missing/linked packet')
    rows=manifest['files']; names=[x['path'] for x in rows]
    require(len(names)==len(set(names)), 'duplicate manifest path')
    for name in names:
        q=PurePosixPath(name)
        require(not q.is_absolute() and '..' not in q.parts and '\\' not in name and q.as_posix()==name,'unsafe member path')
    actual=[]
    for p in packet.rglob('*'):
        require(not p.is_symlink(),'symlink in packet')
        if p.is_file(): actual.append(p.relative_to(packet).as_posix())
        else: require(p.is_dir(),'non-regular packet member')
    require(set(actual)==set(names),'exact membership mismatch')
    for row in rows:
        p=packet/row['path'];b=p.read_bytes()
        require(len(b)==row['bytes'] and digest(b)==row['sha256'],'member bytes mismatch: '+row['path'])
        require(stat.S_IMODE(p.stat().st_mode)==row['mode'],'member mode mismatch: '+row['path'])
        if row.get('working_copy',False):
            q=root/row['path'];require(not q.is_symlink() and q.is_file(),'missing/linked working copy')
            require(q.read_bytes()==b,'working copy mismatch: '+row['path'])
    require('FINAL.md' in names and (packet/'FINAL.md').read_bytes()==(root/'FINAL.md').read_bytes(),'FINAL binding mismatch')
    auth=packet/'private/source-auth.json'
    source_count=0
    if auth.is_file():
        entries=json.loads(auth.read_text());require(len(entries)==25,'source object count')
        for row in entries:
            require(row['local'] in names,'source outside packet')
            b=(packet/row['local']).read_bytes()
            require(len(b)==row['bytes'] and digest(b)==row['sha256'],'source identity mismatch')
            require(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==row['git_blob'],'Git blob mismatch')
            require('/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in row['url'],'pin mismatch')
        source_count=len(entries)
    baseline=packet/'private/r2-baseline.json'
    baseline_count=0
    if baseline.is_file():
        for row in json.loads(baseline.read_text()):
            p=root/row['path'];require(not p.is_symlink() and p.is_file(),'missing r1 baseline')
            b=p.read_bytes();require(len(b)==row['bytes'] and digest(b)==row['sha256'],'r1 baseline changed: '+row['path'])
            baseline_count+=1
    return {'artifact_integrity':'matched','members':len(rows),'source_blobs':source_count,'r1_files_unchanged':baseline_count,'mathematical_verdict':None}

def main():
    a=argparse.ArgumentParser(description=__doc__)
    a.add_argument('--root',required=True)
    a.add_argument('--final-sha256',required=True)
    a.add_argument('--manifest-sha256',required=True)
    a.add_argument('--report-sha256',required=True)
    args=a.parse_args()
    try: print(json.dumps(verify(args.root,args.final_sha256,args.manifest_sha256,args.report_sha256),sort_keys=True))
    except (ValueError,KeyError,OSError,json.JSONDecodeError) as e:
        print('FAILED: '+str(e),file=sys.stderr);return 1
    return 0
if __name__=='__main__': sys.exit(main())
