#!/usr/bin/env python3
"""Parent supplement for the reviewer's detached SEAL; artifact checks only."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import sys


def audit(event, args):
    if event == 'open':
        mode, flags = args[1:3]
        if (isinstance(mode, str) and any(c in mode for c in 'wax+')) or (
            isinstance(flags, int) and flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND)
        ):
            raise PermissionError('WRITE_DENIED')
    if event in {'os.remove', 'os.rmdir', 'os.mkdir', 'os.rename', 'os.link', 'os.symlink',
                 'os.chmod', 'os.chown', 'os.truncate', 'os.utime', 'subprocess.Popen',
                 'os.system', 'os.exec', 'os.posix_spawn', 'os.fork'} or event.startswith('socket.'):
        raise PermissionError('MUTATION_DENIED')


def need(ok, reason):
    if not ok:
        raise ValueError(reason)


def regular(path):
    s = path.lstat()
    need(stat.S_ISREG(s.st_mode) and s.st_nlink == 1, 'REGULAR_SINGLE_LINK')
    return path.read_bytes()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', type=Path, required=True)
    ap.add_argument('--seal-sha256', required=True)
    a = ap.parse_args()
    sys.addaudithook(audit)
    need(re.fullmatch('[a-f0-9]{64}', a.seal_sha256), 'ANCHOR_FORMAT')
    need(stat.S_ISDIR(a.root.lstat().st_mode), 'ROOT_DIRECTORY')
    need({p.name for p in a.root.iterdir()} == {'SEAL.json', 'review.md', 'controls-transcript.txt'}, 'EXACT_INVENTORY')
    b = regular(a.root / 'SEAL.json')
    need(hashlib.sha256(b).hexdigest() == a.seal_sha256, 'DETACHED_SEAL_HASH')
    seal = json.loads(b)
    need(seal['version'] == 1 and seal['pin'] == 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb', 'PIN_SCHEMA')
    need(seal['decision'] == 'TECHNICAL' and seal['conditional_on_correctness'] is True and
         seal['correctness_reviewed'] is False and seal['count_or_gate_assigned'] is False, 'REVIEW_SCOPE')
    need(set(seal['files']) == {'review.md', 'controls-transcript.txt'}, 'SEALED_FILES')
    for name, value in seal['files'].items():
        need(hashlib.sha256(regular(a.root / name)).hexdigest() == value, 'PAYLOAD_HASH:' + name)
    print(json.dumps({'status': 'ARTIFACTS_ONLY', 'decision': seal['decision'],
                      'conditional_on_correctness': True, 'seal_sha256': a.seal_sha256,
                      'files_including_seal': 3, 'mathematical_gate': False}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print('REJECT: ' + str(exc), file=sys.stderr)
        sys.exit(1)
