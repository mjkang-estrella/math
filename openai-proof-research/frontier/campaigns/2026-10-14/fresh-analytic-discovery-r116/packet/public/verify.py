#!/usr/bin/env python3
"""Read-only packet integrity verifier. An external manifest hash is mandatory.
Adapted from the r115 project verifier. This program makes no mathematical, novelty, review, or acceptance decision.
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

def digest(data):
    return hashlib.sha256(data).hexdigest()

def unique(pairs):
    out = {}
    for key, value in pairs:
        if key in out:
            raise ValueError('duplicate JSON key')
        out[key] = value
    return out

def safe(name):
    if not isinstance(name, str) or not name or '\\' in name:
        raise ValueError('invalid member name')
    q = PurePosixPath(name)
    if q.is_absolute() or '..' in q.parts or '.' in q.parts or q.as_posix() != name:
        raise ValueError('unsafe member name')
    return name

def inventory(root):
    root_stat = root.lstat()
    if not stat.S_ISDIR(root_stat.st_mode) or root.is_symlink():
        raise ValueError('packet must be a real directory')
    files, dirs = {}, {}
    for current, subdirs, names in os.walk(root, followlinks=False):
        for name in subdirs + names:
            f = Path(current) / name
            s = f.lstat()
            rel = f.relative_to(root).as_posix()
            if stat.S_ISLNK(s.st_mode):
                raise ValueError('symlink: ' + rel)
            mode = stat.S_IMODE(s.st_mode)
            if stat.S_ISDIR(s.st_mode):
                dirs[rel] = mode
            elif stat.S_ISREG(s.st_mode) and s.st_nlink == 1:
                files[rel] = dict(mode=mode, bytes=s.st_size, sha256=digest(f.read_bytes()))
            else:
                raise ValueError('nonregular or hard-linked member: ' + rel)
    return files, dirs, stat.S_IMODE(root_stat.st_mode)

def verify(root, anchor):
    if not re.fullmatch('[0-9a-f]{64}', anchor):
        raise ValueError('finalhash must be a detached lowercase SHA256')
    if root.is_symlink() or not root.is_dir():
        raise ValueError('invalid packet directory')
    mf = root / 'manifest.json'
    s = mf.lstat()
    if not stat.S_ISREG(s.st_mode) or s.st_nlink != 1:
        raise ValueError('invalid manifest file')
    raw = mf.read_bytes()
    if digest(raw) != anchor:
        raise ValueError('DETACHED manifest anchor mismatch')
    m = json.loads(raw, object_pairs_hook=unique)
    if set(m) != {'schema', 'pin', 'files', 'directories', 'root_mode', 'manifest_mode'}:
        raise ValueError('manifest schema keys')
    if m['schema'] != 'r116-integrity-v1' or m['pin'] != PIN:
        raise ValueError('manifest schema/pin')
    expected = m['files']
    if not isinstance(expected, dict) or not isinstance(m['directories'], dict):
        raise ValueError('manifest inventory types')
    for name, value in expected.items():
        safe(name)
        if name == 'manifest.json' or set(value) != {'mode', 'bytes', 'sha256'}:
            raise ValueError('invalid file record')
        if not re.fullmatch('[0-9a-f]{64}', value['sha256']):
            raise ValueError('invalid member digest')
        if type(value['mode']) is not int or type(value['bytes']) is not int or value['bytes'] < 0:
            raise ValueError('invalid metadata')
    for name in m['directories']:
        safe(name)
    files, dirs, root_mode = inventory(root)
    manifest_record = files.pop('manifest.json')
    if manifest_record['mode'] != m['manifest_mode'] or root_mode != m['root_mode']:
        raise ValueError('root/manifest mode mismatch')
    if files.keys() != expected.keys() or dirs != m['directories']:
        raise ValueError('exact membership/directory metadata mismatch')
    for name, value in expected.items():
        if files[name] != value:
            raise ValueError('file metadata/hash mismatch: ' + name)
    return len(files)

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--packet', required=True, type=Path)
    p.add_argument('--finalhash', required=True, help='independently supplied detached manifest SHA256')
    p.add_argument('--finalfile', required=True, type=Path, help='FINAL.json outside the packet')
    p.add_argument('--finalanchor', required=True, help='independently supplied detached SHA256 of FINAL.json')
    a = p.parse_args()
    try:
        root = a.packet.absolute()
        final = a.finalfile.absolute()
        if final.is_relative_to(root):
            raise ValueError('FINAL must be outside packet')
        fs = final.lstat()
        if not stat.S_ISREG(fs.st_mode) or fs.st_nlink != 1:
            raise ValueError('invalid FINAL file')
        if not re.fullmatch('[0-9a-f]{64}', a.finalanchor):
            raise ValueError('finalanchor must be a detached lowercase SHA256')
        raw_final = final.read_bytes()
        if digest(raw_final) != a.finalanchor:
            raise ValueError('DETACHED FINAL anchor mismatch')
        f = json.loads(raw_final, object_pairs_hook=unique)
        if f['schema'] != 'r116-detached-FINAL-v1' or f['pin'] != PIN:
            raise ValueError('FINAL schema/pin')
        if f['manifest_sha256'] != a.finalhash:
            raise ValueError('FINAL does not bind detached manifest anchor')
        count = verify(root, a.finalhash)
        bindings = {
            'report_sha256': 'public/research-report.md',
            'frozen_target_sha256': 'public/frozen-target.md',
            'proof_sha256': 'public/proof.md',
            'verifier_sha256': 'public/verify.py',
        }
        for key, name in bindings.items():
            if f[key] != digest((root / name).read_bytes()):
                raise ValueError('FINAL binding mismatch: ' + key)
        freeze = json.loads((root / 'public/freeze-receipt.json').read_bytes(), object_pairs_hook=unique)
        if freeze['sha256'] != f['frozen_target_sha256']:
            raise ValueError('frozen target receipt mismatch')
    except (ValueError, OSError, TypeError, KeyError) as e:
        print('INTEGRITY REJECT: ' + str(e), file=sys.stderr)
        return 1
    print(json.dumps(dict(integrity='verified', files=count, manifest_sha256=a.finalhash, final_sha256=a.finalanchor,
                          mathematical_gate=False, contribution_gate=False), sort_keys=True))
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
