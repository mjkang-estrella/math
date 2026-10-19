#!/usr/bin/env python3
"""Copied-tree controls for this review's verify.py; prints JSON only; never writes the packet. MIT."""
import argparse, hashlib, json, os, shutil, subprocess, sys, tempfile
from pathlib import Path
HERE = Path(os.path.abspath(__file__)).parent

def snap(r):
    return {str(p.relative_to(r)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(r.rglob('*')) if p.is_file() and not p.is_symlink()}

def link(r, hard):
    f = r / 'review.md'; side = r.parent / (r.name + '-side.md'); side.write_bytes(f.read_bytes()); f.unlink()
    os.link(side, f) if hard else f.symlink_to(side)

def flip(r):
    b = bytearray((r / 'review.md').read_bytes()); b[0] ^= 1; (r / 'review.md').write_bytes(bytes(b))

def tamper_verdict(r):
    p = r / 'MANIFEST.json'; m = json.loads(p.read_text()); m['verdict'] = 'PASS_FULL_MANUSCRIPT_T298P'; p.write_text(json.dumps(m, indent=1) + '\n')

def main():
    ap = argparse.ArgumentParser(description=__doc__); ap.add_argument('--anchor', required=True); a = ap.parse_args()
    cases = [('positive', None, 'PASS'), ('wrong_anchor', None, 'external manifest anchor'),
             ('append_payload', lambda r: (r / 'review.md').write_bytes((r / 'review.md').read_bytes() + b'\n'), 'payload size'),
             ('same_size_flip', flip, 'payload hash'),
             ('missing_payload', lambda r: (r / 'review.md').unlink(), 'exact sealed membership'),
             ('extra_payload', lambda r: (r / 'EXTRA').write_text('x'), 'exact sealed membership'),
             ('edited_manifest', lambda r: (r / 'MANIFEST.json').write_bytes((r / 'MANIFEST.json').read_bytes() + b'\n'), 'external manifest anchor'),
             ('verdict_tamper', tamper_verdict, 'external manifest anchor'),
             ('symlink', lambda r: link(r, False), 'regular single-link payload'),
             ('hardlink', lambda r: link(r, True), 'regular single-link payload')]
    rows = []
    with tempfile.TemporaryDirectory(prefix='t298p-mr1-ctl-', dir='/var/tmp') as td:
        for name, mut, exp in cases:
            dst = Path(td) / name / 'pkg'; dst.parent.mkdir()
            shutil.copytree(HERE, dst, ignore=shutil.ignore_patterns('__pycache__'))
            if mut: mut(dst)
            anc = ('0' if a.anchor[0] != '0' else '1') + a.anchor[1:] if name == 'wrong_anchor' else a.anchor
            before = snap(dst)
            run = subprocess.run([sys.executable, '-I', '-B', str(dst / 'verify.py'), '--anchor', anc], capture_output=True, text=True)
            out = run.stdout + run.stderr
            ok = ((run.returncode == 0) == (exp == 'PASS')) and exp in out and snap(dst) == before
            rows.append({'case': name, 'expected': exp, 'exit_code': run.returncode, 'matched': ok})
            assert ok, (name, out)
    print(json.dumps({'scope': 'integrity controls only', 'cases': rows}, indent=1))

if __name__ == '__main__':
    main()
