#!/usr/bin/env python3
"""Seal controls for the review r2 packet; MIT, Myeongjin Kang (review packet).

Usage: python3 -I -B seal_controls.py <packet> <anchor>. Runs the packet verifier
(positive, wrong anchor, malformed anchor) and then copies the packet into a
temporary sibling-free directory inside <packet>/.seal-tmp (created and removed
here) to apply one tampering per copy, running the COPY's verify.py with the
original anchor. Prints a summary; writes nothing into the sealed membership.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

packet = Path(sys.argv[1]).absolute()
anchor = sys.argv[2]
wrong = anchor[:-1] + ('0' if anchor[-1] != '0' else '1')


def verify(root, a, via=None):
    script = (via or root) / 'verify.py'
    r = subprocess.run([sys.executable, '-I', '-B', str(script), '--anchor', a],
                       capture_output=True, text=True)
    return r.returncode, (r.stdout + r.stderr).strip()


results = []
results.append(('positive (original, correct anchor)', 0, *verify(packet, anchor)))
results.append(('wrong anchor (last hex digit changed)', 1, *verify(packet, wrong)))
results.append(('malformed anchor', 1, *verify(packet, 'XYZ')))

tmp = packet / '.seal-tmp'
tmp.mkdir()
try:
    def copy(name):
        dest = tmp / name / 'packet'
        shutil.copytree(packet, dest, symlinks=True, ignore=shutil.ignore_patterns('.seal-tmp'))
        return dest

    def case(label, mutate, via=None):
        dest = copy(label.split(':')[0])
        mutate(dest)
        results.append((label, 1, *verify(dest, anchor, via(dest) if via else None)))

    c = copy('C0')
    results.append(('C0: unmodified copy', 0, *verify(c, anchor)))

    def flip(d):
        p = d / 'review.md'
        b = bytearray(p.read_bytes()); b[100] ^= 1; p.write_bytes(bytes(b))
    case('C1: one bit flipped in review.md', flip)
    case('C2: extra file', lambda d: (d / 'checks' / 'extra.txt').write_text('x'))
    case('C3: missing file', lambda d: (d / 'checks' / 'frozen-identity.log').unlink())
    def symlink(d):
        p = d / 'checks' / 'frozen-identity.log'; p.unlink(); p.symlink_to('../review.md')
    case('C4: file replaced by symlink', symlink)
    case('C5: extra empty directory', lambda d: (d / 'checks' / 'empty').mkdir())
    case('C6: FIFO added', lambda d: os.mkfifo(d / 'checks' / 'fifo'))
    def hardlink(d):
        os.link(d / 'review.md', d / 'checks' / 'review-link.md')
    case('C7: hard link added', hardlink)
    def regen(d):
        (d / 'review.md').write_text('tampered\n')
        subprocess.run([sys.executable, '-I', '-B', str(d / 'scripts' / 'make_manifest.py'), str(d)],
                       check=True)
    case('C8: content tampered and manifest regenerated', regen)
    def empty_dir_removed(d):
        shutil.rmtree(d / 'checks' / 'mutations')
    case('C9: directory subtree removed', empty_dir_removed)
    def sym_root(d):
        (d.parent / 'link').symlink_to(d.name)
    case('C10: verifier invoked through symlinked root', sym_root, via=lambda d: d.parent / 'link')
    def manifest_key(d):
        m = d / 'manifest.json'; j = json.loads(m.read_text()); j['extra'] = 1
        m.write_text(json.dumps(j))
    case('C11: manifest edited (anchor no longer matches)', manifest_key)
finally:
    shutil.rmtree(tmp)

ok = True
for label, want, code, out in results:
    passed = (code == 0) == (want == 0)
    ok &= passed
    print('%s | expected %s | exit %d | %s | %s' % (label, 'PASS' if want == 0 else 'FAIL', code,
                                                 'OK' if passed else 'UNEXPECTED', out.splitlines()[-1]))
print('ALL_SEAL_CONTROLS_AS_EXPECTED' if ok else 'SEAL_CONTROL_FAILURE')
print('anchor tested:', anchor)
sys.exit(0 if ok else 1)
