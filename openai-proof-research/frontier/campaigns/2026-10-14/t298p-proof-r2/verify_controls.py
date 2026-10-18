#!/usr/bin/env python3
"""Controls for verify.py, run on a temporary copy (deleted on exit).

Usage: python3 -I -B verify_controls.py > checks/own-verifier-controls.json

The packet is copied without MANIFEST.json; a manifest of the same format
is built for the copy, and then one positive and eight negative controls
are run. The real packet is never written.
"""
import hashlib, json, os, shutil, subprocess, sys, tempfile
from pathlib import Path

SRC = Path(__file__).resolve().parent


def build_manifest(root):
    files = []
    for dirpath, _, filenames in os.walk(root):
        for name in filenames:
            p = Path(dirpath) / name
            rel = p.relative_to(root).as_posix()
            if rel == 'MANIFEST.json':
                continue
            files.append({'path': rel, 'size': p.stat().st_size,
                          'sha256': hashlib.sha256(p.read_bytes()).hexdigest()})
    files.sort(key=lambda e: e['path'])
    man = {'packet': 'T298P proof review round 2', 'verdict': 'PASS_FULL_T298P', 'files': files}
    (root / 'MANIFEST.json').write_text(json.dumps(man, indent=1) + '\n')
    return hashlib.sha256((root / 'MANIFEST.json').read_bytes()).hexdigest()


def fresh(tmp):
    root = Path(tmp) / 'pkt'
    if root.exists():
        shutil.rmtree(root)
    shutil.copytree(SRC, root, ignore=shutil.ignore_patterns('MANIFEST.json', '__pycache__'))
    return root, build_manifest(root)


def run(root, anchor):
    r = subprocess.run([sys.executable, '-I', '-B', str(root / 'verify.py'), '--anchor', anchor],
                       capture_output=True, text=True)
    return r.returncode, (r.stdout + r.stderr).strip()


def edit_manifest(root):
    m = json.loads((root / 'MANIFEST.json').read_text())
    m['files'][0]['sha256'] = '0' * 64
    (root / 'MANIFEST.json').write_text(json.dumps(m, indent=1) + '\n')


def flip_first_byte(root):
    p = root / 'review.md'
    b = bytearray(p.read_bytes())
    b[0] ^= 1
    p.write_bytes(bytes(b))


CONTROLS = [
    ('positive', None, 'PASS', True),
    ('wrong_anchor', 'ANCHOR', 'external manifest anchor', False),
    ('appended_review', lambda r: (r / 'review.md').open('a').write('\n'), 'size review.md', False),
    ('same_size_altered_review', flip_first_byte, 'sha256 review.md', False),
    ('missing_review', lambda r: (r / 'review.md').unlink(), 'exact membership', False),
    ('extra_file', lambda r: (r / 'checks' / 'extra.txt').write_text('x'), 'exact membership', False),
    ('edited_manifest', 'EDIT', 'external manifest anchor', False),
    ('symlink', lambda r: os.symlink('review.md', r / 'link.md'), 'symlink link.md', False),
    ('hardlink', lambda r: os.link(r / 'review.md', r / 'hard.md'), 'nonregular or hardlinked', False),
]

out = []
with tempfile.TemporaryDirectory(dir='/var/tmp', prefix='t298p-r2-ctl-') as tmp:
    for name, action, expect, want_pass in CONTROLS:
        root, anchor = fresh(tmp)
        if action == 'ANCHOR':
            anchor = 'f' * 64
        elif action == 'EDIT':
            edit_manifest(root)
        elif action is not None:
            action(root)
        rc, msg = run(root, anchor)
        ok = (rc == 0) == want_pass and expect in msg
        out.append({'control': name, 'rc': rc, 'expected': expect, 'observed': msg[:160], 'ok': ok})
print(json.dumps({'all_ok': all(c['ok'] for c in out), 'controls': out,
                  'scope': 'identity controls of verify.py on a temporary copy; no mathematical verdict'},
                 indent=1))
