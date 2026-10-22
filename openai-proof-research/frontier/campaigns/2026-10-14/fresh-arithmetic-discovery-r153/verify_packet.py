#!/usr/bin/env python3
"""Read-only exact-packet verification. Trust only explicit detached hash arguments."""
import argparse, hashlib, json, os
from pathlib import Path, PurePosixPath

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def verify(packet, manifest, report, final_sha, manifest_sha, report_sha):
    if packet.is_symlink() or manifest.is_symlink() or report.is_symlink():
        raise ValueError('symlink at an explicit anchor')
    if digest(manifest) != manifest_sha:
        raise ValueError('manifest anchor mismatch')
    if digest(report) != report_sha:
        raise ValueError('report anchor mismatch')
    m=json.loads(manifest.read_text())
    r=json.loads(report.read_text())
    if m.get('schema') != 'r153-exact-packet-v1':
        raise ValueError('unknown manifest schema')
    if r.get('final_sha256') != final_sha or r.get('manifest_sha256') != manifest_sha:
        raise ValueError('report does not bind supplied anchors')
    expected={}
    for item in m['files']:
        name=item['path']; rel=PurePosixPath(name)
        if rel.is_absolute() or '..' in rel.parts or name != rel.as_posix() or name in expected:
            raise ValueError('unsafe or duplicate manifest path')
        expected[name]=item
    actual=set(); dirs=set()
    for base, subdirs, files in os.walk(packet,followlinks=False):
        b=Path(base)
        for n in subdirs:
            f=b/n
            if f.is_symlink(): raise ValueError('symlink in packet')
            dirs.add(f.relative_to(packet).as_posix())
        for n in files:
            f=b/n
            if f.is_symlink() or not f.is_file(): raise ValueError('non-regular packet file')
            actual.add(f.relative_to(packet).as_posix())
    if actual != set(expected): raise ValueError('packet file inventory mismatch')
    if dirs != set(m['directories']): raise ValueError('packet directory inventory mismatch')
    for name, item in expected.items():
        f=packet/name
        if f.stat().st_size != item['bytes'] or digest(f) != item['sha256']:
            raise ValueError('content mismatch: '+name)
    if digest(packet/'FINAL.md') != final_sha:
        raise ValueError('FINAL anchor mismatch')
    if r.get('packet_files') != len(expected): raise ValueError('report count mismatch')
    return {'artifact_status':'MATCH','packet_files':len(expected),'final_sha256':final_sha,'manifest_sha256':manifest_sha,'report_sha256':report_sha,'read_only':True,'mathematical_gate':False}

if __name__=='__main__':
    a=argparse.ArgumentParser()
    for n in ['packet','manifest','report','final-sha','manifest-sha','report-sha']:
        a.add_argument('--'+n,required=True)
    x=a.parse_args()
    try:
        print(json.dumps(verify(Path(x.packet),Path(x.manifest),Path(x.report),x.final_sha,x.manifest_sha,x.report_sha),indent=2))
    except (ValueError,OSError,KeyError,TypeError,json.JSONDecodeError) as e:
        print(json.dumps({'artifact_status':'REJECT','reason':str(e),'mathematical_gate':False}))
        raise SystemExit(1)
