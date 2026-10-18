#!/usr/bin/env python3
"""Copied positive and reason-checked negative controls for verify_review.py.

Copies the sealed review directory into fresh scratch space under /var/tmp,
runs the positive control with the externally supplied seal, then four
tampered copies, each required to fail with its specific reason. Scratch
copies only; the sealed tree is never modified. Integrity controls only;
no mathematical content is certified by any run."""
import argparse, json, os, pathlib, shutil, subprocess, sys, tempfile

SCRATCH = '/var/tmp'

def run_verifier(tree, seal):
    return subprocess.run(
        [sys.executable, '-B', str(tree / 'verify_review.py'),
         '--manifest-sha256', seal],
        capture_output=True, text=True)

def fresh_copy(src, tag):
    dst = pathlib.Path(tempfile.mkdtemp(prefix='t338n-control-' + tag + '-',
                                        dir=SCRATCH)) / 'tree'
    shutil.copytree(src, dst, symlinks=False)
    return dst

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--seal', required=True,
                    help='external SHA256 of the sealed MANIFEST.json')
    ap.add_argument('--src', type=pathlib.Path,
                    default=pathlib.Path(__file__).resolve().parent)
    a = ap.parse_args()
    src = a.src.resolve()
    require_src = src / 'MANIFEST.json'
    if not require_src.is_file():
        print('FAIL: source tree has no MANIFEST.json', file=sys.stderr)
        sys.exit(1)
    results = []

    # Positive control: untouched copy must pass with the external seal.
    pos = fresh_copy(src, 'positive')
    r = run_verifier(pos, a.seal)
    ok = r.returncode == 0 and 'PASS_IDENTITY_ONLY' in r.stdout
    results.append({'control': 'positive_unmodified_copy',
                    'expected': 'PASS_IDENTITY_ONLY',
                    'observed': r.stdout.strip() or r.stderr.strip(),
                    'pass': bool(ok)})

    # Negative 1: wrong external anchor.
    t = fresh_copy(src, 'wrong-anchor')
    r = run_verifier(t, '0' * 64)
    ok = r.returncode != 0 and 'anchor mismatch' in r.stderr
    results.append({'control': 'wrong_external_anchor',
                    'expected_rejection': 'anchor mismatch',
                    'observed': r.stderr.strip(), 'pass': bool(ok)})

    # Negative 2: one flipped byte in a payload file.
    t = fresh_copy(src, 'tampered-payload')
    target = t / 'review.md'
    data = target.read_bytes()
    target.write_bytes(bytes([data[0] ^ 1]) + data[1:])
    r = run_verifier(t, a.seal)
    ok = r.returncode != 0 and 'payload hash mismatch' in r.stderr
    results.append({'control': 'flipped_byte_in_review_md',
                    'expected_rejection': 'payload hash mismatch',
                    'observed': r.stderr.strip(), 'pass': bool(ok)})

    # Negative 3: planted symlink inside the tree.
    t = fresh_copy(src, 'planted-link')
    os.symlink('review.md', t / 'planted-link.md')
    r = run_verifier(t, a.seal)
    ok = r.returncode != 0 and 'link' in r.stderr
    results.append({'control': 'planted_symlink',
                    'expected_rejection': 'link rejection',
                    'observed': r.stderr.strip(), 'pass': bool(ok)})

    # Negative 4: extra unexpected regular file.
    t = fresh_copy(src, 'extra-file')
    (t / 'unexpected.md').write_text('unexpected payload\n')
    r = run_verifier(t, a.seal)
    ok = r.returncode != 0 and 'membership mismatch' in r.stderr
    results.append({'control': 'extra_unexpected_file',
                    'expected_rejection': 'membership mismatch',
                    'observed': r.stderr.strip(), 'pass': bool(ok)})

    # Negative 5: removed payload file.
    t = fresh_copy(src, 'removed-file')
    (t / 'run_controls.py').unlink()
    r = run_verifier(t, a.seal)
    ok = r.returncode != 0 and 'membership mismatch' in r.stderr
    results.append({'control': 'removed_payload_file',
                    'expected_rejection': 'membership mismatch',
                    'observed': r.stderr.strip(), 'pass': bool(ok)})

    overall = all(x['pass'] for x in results)
    print(json.dumps({'status': 'PASS_ALL_CONTROLS' if overall
                      else 'FAIL_CONTROLS',
                      'controls': results,
                      'mathematics_verified': False}, indent=2))
    sys.exit(0 if overall else 1)

if __name__ == '__main__':
    main()
