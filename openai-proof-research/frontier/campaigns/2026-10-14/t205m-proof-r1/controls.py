#!/usr/bin/env python3
"""MIT. Copied mutation controls for this review's verifier.
Usage: controls.py EXTERNAL_MANIFEST_SHA256 SCRATCH_PARENT_UNDER_/var/tmp
Every mutation is applied to a fresh copy under the scratch parent; the
directory containing this script is only read. Output goes to stdout.
"""
import json, os, shutil, subprocess, sys, tempfile
from pathlib import Path


def run(d, anchor):
    c = subprocess.run([sys.executable, str(d / 'verify.py'), anchor], capture_output=True, text=True)
    return {'returncode': c.returncode, 'output': (c.stdout + c.stderr).strip()}


def main(anchor, parent):
    parent = Path(parent).resolve()
    if not str(parent).startswith('/var/tmp/'):
        raise SystemExit('scratch parent must be under /var/tmp')
    src = Path(os.path.abspath(__file__)).parent
    scratch = Path(tempfile.mkdtemp(prefix='t205m-proof-r1-controls-', dir=parent))
    expect = {'payload': 'file inventory mismatch', 'missing': 'file inventory mismatch',
              'extra_file': 'file inventory mismatch', 'extra_dir': 'directory inventory mismatch',
              'root_symlink': 'symlink ancestor', 'hardlink': 'hardlink:', 'fifo': 'nonregular entry:',
              'nested_manifest': 'nested manifest', 'self_reseal': 'external manifest anchor mismatch',
              'wrong_anchor': 'external manifest anchor mismatch'}
    cases = {}
    try:
        for name in ['unchanged_copy', *expect]:
            case = scratch / name; case.mkdir(); cp = case / 'pkt'; shutil.copytree(src, cp)
            target, used = cp, anchor
            if name == 'payload':
                with (cp / 'review.md').open('a') as f: f.write('\nmutation\n')
            elif name == 'missing': (cp / 'review.md').unlink()
            elif name == 'extra_file': (cp / 'extra').write_text('x')
            elif name == 'extra_dir': (cp / 'extra-dir').mkdir()
            elif name == 'root_symlink':
                target = case / 'link'; target.symlink_to(cp, target_is_directory=True)
            elif name == 'hardlink':
                o = case / 'outside'; shutil.copyfile(cp / 'review.md', o); (cp / 'review.md').unlink(); os.link(o, cp / 'review.md')
            elif name == 'fifo': os.mkfifo(cp / 'pipe')
            elif name == 'nested_manifest':
                (cp / 'nested').mkdir(); (cp / 'nested' / 'manifest.json').write_text('{}')
            elif name == 'self_reseal':
                import hashlib
                f = cp / 'review.md'; f.write_text(f.read_text() + '\nmutation\n')
                m = json.loads((cp / 'manifest.json').read_text())
                m['files']['review.md'] = {'bytes': f.stat().st_size, 'sha256': hashlib.sha256(f.read_bytes()).hexdigest()}
                (cp / 'manifest.json').write_text(json.dumps(m, indent=1, sort_keys=True) + '\n')
            elif name == 'wrong_anchor': used = '0' * 64
            r = run(target, used); cases[name] = r
            if name == 'unchanged_copy':
                assert r['returncode'] == 0, r
            else:
                assert r['returncode'] != 0 and expect[name] in r['output'], (name, r)
        return {'status': 'PASS_11_COPIED_CONTROLS', 'anchor': anchor, 'cases': cases}
    finally:
        shutil.rmtree(scratch)


if __name__ == '__main__':
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    print(json.dumps(main(sys.argv[1], sys.argv[2]), indent=1))
