#!/usr/bin/env python3
"""Read-only verification of an explicitly anchored packet; no discovery or writes."""
import argparse, hashlib, json, os
from pathlib import Path

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def verify(packet, manifest, report, final_sha, manifest_sha, report_sha):
    packet, manifest, report = map(Path, (packet, manifest, report))
    if any(p.is_symlink() for p in (packet, manifest, report, packet/'FINAL.md')):
        raise ValueError('symlink anchor')
    for p, expected in [(packet/'FINAL.md', final_sha), (manifest, manifest_sha), (report, report_sha)]:
        if len(expected) != 64 or digest(p) != expected:
            raise ValueError('detached anchor mismatch: '+str(p))
    data = json.loads(manifest.read_text())
    files = data['files']
    wanted = set()
    for e in files:
        rel = e['path']
        rp = Path(rel)
        if rp.is_absolute() or '..' in rp.parts or rp.as_posix() != rel or rel in wanted:
            raise ValueError('invalid or duplicate member')
        wanted.add(rel)
        p = packet/rp
        check = packet
        for component in rp.parts:
            check = check/component
            if check.is_symlink():
                raise ValueError('symlink member')
        if not p.is_file() or p.stat().st_size != e['bytes'] or digest(p) != e['sha256']:
            raise ValueError('member mismatch: '+rel)
    actual = set()
    for directory, dirs, names in os.walk(packet, followlinks=False):
        for name in dirs + names:
            if (Path(directory)/name).is_symlink():
                raise ValueError('symlink in packet')
        for name in names:
            actual.add((Path(directory)/name).relative_to(packet).as_posix())
    if actual != wanted:
        raise ValueError('packet member set mismatch')
    return {'verified_files':len(files),'verified_bytes':sum(x['bytes'] for x in files),'read_only':True,'mathematical_gate':False}

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    for arg in ('packet','manifest','report','final-sha256','manifest-sha256','report-sha256'):
        ap.add_argument('--'+arg,required=True)
    a=ap.parse_args()
    print(json.dumps(verify(a.packet,a.manifest,a.report,a.final_sha256,a.manifest_sha256,a.report_sha256),sort_keys=True))
