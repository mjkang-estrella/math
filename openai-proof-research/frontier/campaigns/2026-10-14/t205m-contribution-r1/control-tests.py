#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang
"""Mutation controls for verify.py. Every case runs on a copy in a fresh
temporary directory (honours TMPDIR; the copies need about 5 MB each, so a
small /tmp quota may require TMPDIR=/var/tmp). This packet is never modified."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile


def run(script, anchor, author):
    proc = subprocess.run([sys.executable, str(script), '--anchor', anchor, '--author-root', str(author)],
                          capture_output=True, text=True)
    return {'returncode': proc.returncode, 'output': (proc.stdout + proc.stderr).strip()}


def writable_copy(src, dst):
    shutil.copytree(src, dst, symlinks=True)
    for root, dirs, files in os.walk(dst):
        for name in dirs + files:
            path = os.path.join(root, name)
            os.chmod(path, os.lstat(path).st_mode | 0o200)


def reseal(packet):
    path = packet / 'manifest.json'
    manifest = json.loads(path.read_text())
    for row in manifest['files']:
        data = (packet / row['path']).read_bytes()
        row['bytes'], row['sha256'] = len(data), hashlib.sha256(data).hexdigest()
    path.write_text(json.dumps(manifest, indent=2) + '\n')


MUTATIONS = {
    'unchanged_copy': lambda p, c: None,
    'payload': lambda p, c: (p / 'review.md').write_bytes((p / 'review.md').read_bytes() + b'x'),
    'primary_payload': lambda p, c: (p / 'private/primary/kirillov-hep-th9304099.pdf').write_bytes(b'0'),
    'missing': lambda p, c: (p / 'reading-limits.md').unlink(),
    'extra_file': lambda p, c: (p / 'extra.md').write_text('x'),
    'extra_empty_directory': lambda p, c: (p / 'extra-dir').mkdir(),
    'symlink_entry': lambda p, c: (p / 'link.md').symlink_to('review.md'),
    'hardlink': lambda p, c: os.link(p / 'review.md', c / 'outside-hardlink'),
    'fifo': lambda p, c: os.mkfifo(p / 'pipe'),
    'nested_manifest': lambda p, c: (p / 'private/manifest.json').write_text('{}'),
    'self_reseal': lambda p, c: ((p / 'review.md').write_text('Verdict: DUPLICATE\n'), reseal(p)),
}


def main(anchor):
    root = Path(os.path.abspath(__file__)).parent
    author = (root.parent / 'fresh-arithmetic-discovery-r38').resolve()
    scratch = Path(os.path.realpath(tempfile.mkdtemp(prefix='t205m-contribution-controls-')))
    cases = {'canonical': run(root / 'verify.py', anchor, author)}
    assert cases['canonical']['returncode'] == 0, cases['canonical']
    try:
        for name, mutate in MUTATIONS.items():
            case = scratch / name
            case.mkdir()
            packet = case / 'packet'
            writable_copy(root, packet)
            mutate(packet, case)
            cases[name] = run(packet / 'verify.py', anchor, author)
        for name in ('root_symlink', 'ancestor_symlink'):
            case = scratch / name
            case.mkdir()
            writable_copy(root, case / 'packet')
            if name == 'root_symlink':
                (case / 'link').symlink_to(case / 'packet', target_is_directory=True)
                script = case / 'link' / 'verify.py'
            else:
                (scratch / 'ancestor-link').symlink_to(case, target_is_directory=True)
                script = scratch / 'ancestor-link' / 'packet' / 'verify.py'
            cases[name] = run(script, anchor, author)
        cases['wrong_anchor'] = run(root / 'verify.py', '0' * 64, author)
    finally:
        shutil.rmtree(scratch)
    passing = {'canonical', 'unchanged_copy'}
    ok = all((c['returncode'] == 0) == (n in passing) for n, c in cases.items())
    return {'status': f'PASS_{len(cases)}_CONTROLS' if ok else 'CONTROL_FAILURE',
            'anchor': anchor, 'cases': cases,
            'limits': 'Byte and membership integrity only; no mathematical or contribution check.'}


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise SystemExit('usage: control-tests.py EXTERNAL_MANIFEST_SHA256')
    result = main(sys.argv[1])
    print(json.dumps(result, indent=2))
    sys.exit(0 if result['status'].startswith('PASS') else 1)
