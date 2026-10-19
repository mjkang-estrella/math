#!/usr/bin/env python3
"""Read-only byte authentication, not a mathematical gate.
Adapted from arithmetic r82 (and its r81 predecessor). MIT; Myeongjin Kang.
Requires a caller-supplied detached FINAL hash; never writes or reseals.
"""
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
    if not isinstance(name, str):
        fail('unsafe manifest path type')
    p = PurePosixPath(name)
    if not name or p.is_absolute() or any(x in ('..', '.') for x in p.parts) or str(p) != name or '\\' in name:
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
    if final.get('schema') != 'r83-detached-final-v1':
        fail('unknown FINAL schema')
    manifest_bytes = regular(root / 'MANIFEST.json')
    report_bytes = regular(root / 'REPORT.md')
    if sha(manifest_bytes) != final['manifest_sha256'] or sha(report_bytes) != final['report_sha256']:
        fail('detached manifest/report mismatch')
    manifest = json.loads(manifest_bytes)
    if manifest.get('schema') != 'r83-exact-packet-v1' or manifest.get('pin') != PIN:
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
    if selection['pin'] != PIN or selection['entry_count'] != 13223 or selection['truncated'] is not False:
        fail('complete-tree receipt mismatch')
    if selection['tree_sha256'] != 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b':
        fail('complete-tree identity mismatch')
    canonical = {e['path']: e for e in selection['entries']}
    if len(canonical) != len(selection['entries']):
        fail('duplicate selected canonical path')
    source = json.loads(regular(packet / 'public/source-register.json'))
    if len(source) != len(canonical) or {e['canonical_path'] for e in source} != set(canonical):
        fail('canonical selection mismatch')
    for e in source:
        safe_relative(e['path'])
        if not e['path'].startswith('private/upstream/'):
            fail('unexpected source storage')
        b = regular(packet / e['path'])
        blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        c = canonical[e['canonical_path']]
        if blob != e['git_blob'] or blob != c['sha'] or len(b) != c['size'] or len(b) != e['size'] or sha(b) != e['sha256']:
            fail('canonical blob mismatch')
        if e['raw_url'] != 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + e['canonical_path']:
            fail('unpinned raw URL')
    primary = json.loads(regular(packet / 'public/primary-register.json'))
    for e in primary:
        if e.get('status') != 200:
            continue
        for field, digest in [('pdf_path', 'pdf_sha256'), ('text_path', 'text_sha256')]:
            safe_relative(e[field])
            if not e[field].startswith('private/primary/'):
                fail('unexpected primary storage')
            if sha(regular(packet / e[field])) != e[digest]:
                fail('primary identity mismatch')
    history = json.loads(regular(packet / 'private/history-provenance.json'))
    for e in history:
        safe_relative(e['packet_path'])
        if not e['packet_path'].startswith('private/history/'):
            fail('unexpected history storage')
        b = regular(packet / e['packet_path'])
        if sha(b) != e['sha256'] or len(b) != e['bytes']:
            fail('history identity mismatch')
    print(json.dumps({'result': 'INTEGRITY_ONLY_OK', 'packet_files': len(actual),
                      'canonical_source_blobs': len(source), 'primary_pdfs': sum(e.get('status') == 200 for e in primary),
                      'retained_history_bodies': len(history),
                      'mathematical_verification': False}, sort_keys=True))

if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, TypeError) as exc:
        print('INTEGRITY_REJECTED: ' + str(exc), file=sys.stderr)
        sys.exit(1)
