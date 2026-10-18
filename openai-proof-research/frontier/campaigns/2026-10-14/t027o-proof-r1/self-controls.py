#!/usr/bin/env python3
"""MIT. Positive/wrong-anchor and copied mutation controls for this review directory.

Mutations run only on disposable copies under /var/tmp. Prints results; writes nothing here.
"""
import hashlib, json, os, shutil, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(os.path.abspath(__file__)).parent

def run(p, anchor):
    c = subprocess.run([sys.executable, '-B', str(p / 'verify.py'), anchor], capture_output=True, text=True)
    return {'returncode': c.returncode, 'output': (c.stdout + c.stderr).strip()}

def main(anchor):
    cases = {'in_place': run(ROOT, anchor), 'in_place_wrong_anchor': run(ROOT, 'f' * 64)}
    scratch = Path(tempfile.mkdtemp(prefix='t027o-proof-r1-self-', dir='/var/tmp'))
    try:
        for name in ['unchanged_copy', 'review_byte', 'missing_file', 'extra_file', 'extra_dir', 'symlink_file',
                     'root_symlink', 'hardlink', 'fifo', 'nested_manifest', 'self_reseal_old_anchor']:
            case = scratch / name; case.mkdir(); copy = case / 'r'
            shutil.copytree(ROOT, copy, symlinks=True); target = copy
            if name == 'review_byte':
                p = copy / 'review.md'; b = bytearray(p.read_bytes()); b[200] ^= 1; p.write_bytes(bytes(b))
            elif name == 'missing_file': (copy / 'reviewer-diagnostic.json').unlink()
            elif name == 'extra_file': (copy / 'x').write_text('x')
            elif name == 'extra_dir': (copy / 'd').mkdir()
            elif name == 'symlink_file':
                (copy / 'review.md').unlink(); (copy / 'review.md').symlink_to(ROOT / 'review.md')
            elif name == 'root_symlink':
                target = case / 'link'; target.symlink_to(copy, target_is_directory=True)
            elif name == 'hardlink':
                o = case / 'o'; shutil.copyfile(copy / 'review.md', o); (copy / 'review.md').unlink(); os.link(o, copy / 'review.md')
            elif name == 'fifo': os.mkfifo(copy / 'pipe')
            elif name == 'nested_manifest': (copy / 'sub').mkdir(); (copy / 'sub/manifest.json').write_text('{}')
            elif name == 'self_reseal_old_anchor':
                p = copy / 'review.md'; p.write_text(p.read_text().replace('PASS_FULL_T027O', 'FAIL_T027O', 1))
                m = json.loads((copy / 'manifest.json').read_text())
                m['files']['review.md'] = {'bytes': p.stat().st_size, 'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
                (copy / 'manifest.json').write_text(json.dumps(m, indent=2, sort_keys=True) + '\n')
            res = run(target, anchor); res['as_expected'] = (res['returncode'] == 0) == (name == 'unchanged_copy')
            cases[name] = res; shutil.rmtree(case)
    finally:
        shutil.rmtree(scratch, ignore_errors=True)
    ok = cases['in_place']['returncode'] == 0 and cases['in_place_wrong_anchor']['returncode'] == 1 and \
        all(v['as_expected'] for k, v in cases.items() if 'as_expected' in v)
    print(json.dumps({'status': 'PASS' if ok else 'FAIL', 'anchor': anchor, 'cases': cases}, indent=1))
    return 0 if ok else 1

if __name__ == '__main__':
    if len(sys.argv) != 2: raise SystemExit('usage: self-controls.py EXTERNAL_MANIFEST_SHA256')
    sys.exit(main(sys.argv[1]))
