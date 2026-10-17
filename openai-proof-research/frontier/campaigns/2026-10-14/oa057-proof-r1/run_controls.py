#!/usr/bin/env python3
"""Integrity controls for verify.py. Writes only to a temporary directory.
Usage: python3 -I -B run_controls.py --expected-manifest-sha256 <hex>"""
import argparse, json, shutil, subprocess, sys, tempfile
from pathlib import Path


def run(args):
    r = subprocess.run([sys.executable, '-I', '-B'] + args, capture_output=True, text=True, timeout=60)
    return r.returncode, (r.stdout + r.stderr).strip()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--expected-manifest-sha256', required=True)
    h = ap.parse_args().expected_manifest_sha256
    root = Path(__file__).resolve().parent
    v = str(root / 'verify.py')
    wrong = ('0' if h[0] != '0' else '1') + h[1:]
    res = {}
    res['positive'] = run([v, '--expected-manifest-sha256', h])
    res['wrong_anchor'] = run([v, '--expected-manifest-sha256', wrong])
    res['malformed_anchor'] = run([v, '--expected-manifest-sha256', 'xyz'])
    with tempfile.TemporaryDirectory() as t:
        c = Path(t) / 'pkg'
        shutil.copytree(root, c, ignore=shutil.ignore_patterns('__pycache__'))
        res['copy_positive'] = run([v, '--root', str(c), '--skip-author', '--expected-manifest-sha256', h])
        rp = c / 'report.md'
        b = bytearray(rp.read_bytes()); b[100] ^= 1; rp.write_bytes(bytes(b))
        res['tampered_report'] = run([v, '--root', str(c), '--skip-author', '--expected-manifest-sha256', h])
        b[100] ^= 1; rp.write_bytes(bytes(b))
        (c / 'extra.txt').write_text('x')
        res['extra_file'] = run([v, '--root', str(c), '--skip-author', '--expected-manifest-sha256', h])
    expect = {'positive': 0, 'copy_positive': 0}
    ok = all((rc == 0) == (expect.get(k, 1) == 0) for k, (rc, _) in res.items())
    print(json.dumps({'controls_ok': ok, 'results': {k: {'rc': rc, 'out': o[-160:]} for k, (rc, o) in res.items()}}, indent=1, sort_keys=True))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
