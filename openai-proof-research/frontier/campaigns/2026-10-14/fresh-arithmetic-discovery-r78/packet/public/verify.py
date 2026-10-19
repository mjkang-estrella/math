#!/usr/bin/env python3
"""Read-only byte authentication, not a mathematical gate. MIT; Myeongjin Kang."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'

def fail(message):
    raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def regular(path):
    st = path.lstat()
    if not stat.S_ISREG(st.st_mode):
        fail('not a regular file: ' + str(path))
    return path.read_bytes()

def safe_relative(name):
    p = PurePosixPath(name)
    if not isinstance(name, str) or not name or p.is_absolute() or any(x in ('..', '.') for x in p.parts) or str(p) != name or '\\' in name:
        fail('unsafe manifest path')
    return p

def scan(base):
    files, dirs = {}, []
    for here, ds, fs in os.walk(base, followlinks=False):
        for name in ds:
            p = Path(here) / name
            if not stat.S_ISDIR(p.lstat().st_mode):
                fail('non-directory/symlink: ' + str(p))
            dirs.append(p.relative_to(base).as_posix())
        for name in fs:
            p = Path(here) / name
            b = regular(p)
            files[p.relative_to(base).as_posix()] = {'bytes': len(b), 'sha256': sha(b)}
    return files, sorted(dirs)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True, type=Path)
    ap.add_argument('--finalhash', required=True, help='Detached SHA256 of FINAL.json')
    args = ap.parse_args()
    if not re.fullmatch('[0-9a-f]{64}', args.finalhash):
        fail('finalhash must be a detached lowercase SHA256')
    root = args.root.absolute()
    if root.is_symlink() or not root.is_dir():
        fail('root must be an actual directory')
    packet = root / 'packet'
    if packet.is_symlink() or not packet.is_dir():
        fail('packet must be an actual directory')
    final_bytes = regular(root / 'FINAL.json')
    if sha(final_bytes) != args.finalhash:
        fail('FINAL external anchor mismatch')
    final = json.loads(final_bytes)
    if final.get('schema') != 'r78-detached-final-v1':
        fail('unknown FINAL schema')
    manifest_bytes = regular(root / 'MANIFEST.json')
    report_bytes = regular(root / 'REPORT.md')
    if sha(manifest_bytes) != final['manifest_sha256'] or sha(report_bytes) != final['report_sha256']:
        fail('detached manifest/report mismatch')
    manifest = json.loads(manifest_bytes)
    if manifest.get('schema') != 'r78-exact-packet-v1' or manifest.get('pin') != PIN:
        fail('manifest schema/pin mismatch')
    entries = manifest['files']
    if len({e['path'] for e in entries}) != len(entries):
        fail('duplicate manifest member')
    expected = {}
    for e in entries:
        safe_relative(e['path'])
        expected[e['path']] = {'bytes': e['bytes'], 'sha256': e['sha256']}
    for d in manifest['directories']:
        safe_relative(d)
    actual, directories = scan(packet)
    if actual != expected or directories != manifest['directories']:
        fail('packet bytes or exact membership mismatch')
    selection = json.loads(regular(packet / 'private/canonical-selection.json'))
    if selection['commit'] != PIN or selection['entries'] != 13223 or selection['truncated'] is not False:
        fail('complete-tree receipt mismatch')
    canonical = {e['path']: e for e in selection['selected']}
    source = json.loads(regular(packet / 'private/source-provenance.json'))
    if {e['path'] for e in source} != set(canonical):
        fail('canonical selection mismatch')
    for e in source:
        safe_relative(e['retained'])
        b = regular(packet / e['retained'])
        blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        c = canonical[e['path']]
        if blob != e['sha'] or blob != c['sha'] or len(b) != c['size'] or sha(b) != e['sha256']:
            fail('canonical blob mismatch')
        if e['raw_url'] != 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + e['path']:
            fail('unpinned raw URL')
    primary = json.loads(regular(packet / 'private/primary-provenance.json'))
    for e in primary:
        if e['status'] != 'success':
            continue
        if not re.fullmatch('[a-z0-9-]+', e['key']):
            fail('unsafe primary key')
        for suffix, field in [('.pdf', 'pdf_sha256'), ('.txt', 'text_sha256')]:
            if sha(regular(packet / 'private/primary' / (e['key'] + suffix))) != e[field]:
                fail('primary identity mismatch')
    print(json.dumps({'result': 'INTEGRITY_ONLY_OK', 'packet_files': len(actual),
                      'canonical_source_blobs': len(source), 'primary_pdfs': sum(e['status']=='success' for e in primary),
                      'mathematical_verification': False}, sort_keys=True))

if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, TypeError) as exc:
        print('INTEGRITY_REJECTED: ' + str(exc), file=sys.stderr)
        sys.exit(1)
