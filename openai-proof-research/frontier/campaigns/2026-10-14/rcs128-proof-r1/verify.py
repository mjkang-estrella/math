# Reviewer verifier (rcs128-proof-r1). SPDX-License-Identifier: MIT
"""Read-only verification of this review directory.

    python3 -B verify.py --expected-manifest-sha256 EXTERNAL_SHA256 [--replay]

1. The caller-supplied external hash must equal SHA256(MANIFEST.json); otherwise FAIL
   before anything else is checked.
2. Exact inventory: every file except MANIFEST.json is listed with size and SHA256,
   no extras, no symlinks, no __pycache__.
3. The four frozen author anchors in ../fresh-structural-discovery-r37 match.
4. --replay re-runs the pinned finite diagnostics (PYTHONHASHSEED=0, -B) and compares
   stdout byte-for-byte with replay-expected.json.  Nothing is written.
Integrity and finite diagnostics only; not a proof."""
import argparse, hashlib, json, os, subprocess, sys
from pathlib import Path

AUTHOR = {
    'MANIFEST.json': 'a81ea2335db99c097423af9baf5abd272fa556ab6f08d870b8d184ee23bb96a6',
    'candidate.md': 'ebfed67a43a306af4788c39300e2a418f82193c826bae130508fd87955d39137',
    'original-scope.txt': '7dfa38dbfdc0298863bbd29c76af27061d9f033cf67aa0800979e3310de1eb60',
    'checkpoint.md': '3ab70804621cccba5319e45b18f21b267b3ac8d3cf15deb1aa59f8d415085bf0',
}


def sha(b):
    return hashlib.sha256(b).hexdigest()


def need(ok, msg):
    if not ok:
        raise ValueError(msg)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--expected-manifest-sha256', required=True)
    ap.add_argument('--replay', action='store_true')
    a = ap.parse_args()
    root = Path(__file__).resolve().parent
    raw = (root / 'MANIFEST.json').read_bytes()
    need(sha(raw) == a.expected_manifest_sha256, 'external manifest anchor mismatch')
    man = json.loads(raw)
    names = [r['path'] for r in man['files']]
    need(len(names) == len(set(names)), 'duplicate path')
    need(all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in names), 'unsafe path')
    actual = []
    for p in root.rglob('*'):
        need(not p.is_symlink(), 'symlink present')
        need('__pycache__' not in p.parts, 'bytecode cache present')
        if p.is_file() and p != root / 'MANIFEST.json':
            actual.append(p.relative_to(root).as_posix())
    need(sorted(actual) == sorted(names), 'exact inventory mismatch')
    for r in man['files']:
        b = (root / r['path']).read_bytes()
        need(len(b) == r['size'] and sha(b) == r['sha256'], 'payload mismatch: ' + r['path'])
    adir = root.parent / 'fresh-structural-discovery-r37'
    for n, h in AUTHOR.items():
        need(sha((adir / n).read_bytes()) == h, 'author anchor mismatch: ' + n)
    if a.replay:
        exp = json.loads((root / 'replay-expected.json').read_text())
        env = dict(os.environ, PYTHONHASHSEED='0', PYTHONDONTWRITEBYTECODE='1')
        for run in exp['runs']:
            out = subprocess.run([sys.executable, '-B', str(root / run['script'])] + run['args'],
                                 cwd=str(root), env=env, capture_output=True, text=True, check=True)
            need(out.stdout == run['stdout'], 'replay mismatch: ' + run['script'])
    print(json.dumps(dict(status='PASS', payload_files=len(names), author_anchors=len(AUTHOR), replayed=a.replay,
                          meaning='integrity and bounded diagnostics only; verdict rests on review.md proof re-derivation')))


if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        print('FAIL: ' + str(e), file=sys.stderr)
        sys.exit(1)
