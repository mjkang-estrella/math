#!/usr/bin/env python3
"""MIT. Copied integrity controls. Run only from a disposable copy; all scratch goes to a new /var/tmp directory."""
import json, os, shutil, subprocess, sys, tempfile
from pathlib import Path


def run(p, anchor):
    c = subprocess.run([sys.executable, '-B', str(p / 'verify.py'), anchor], capture_output=True, text=True)
    return {'returncode': c.returncode, 'output': (c.stdout + c.stderr).strip()}


def main(anchor):
    root = Path(os.path.abspath(__file__)).parent
    scratch = Path(tempfile.mkdtemp(prefix='t250p-proof-r1-controls-', dir='/var/tmp'))
    cases = {}
    try:
        for name in ['unchanged_copy', 'payload', 'missing', 'extra_file', 'extra_empty_directory', 'root_symlink',
                     'ancestor_symlink', 'hardlink', 'fifo', 'nested_manifest', 'self_reseal', 'wrong_anchor']:
            case = scratch / name
            case.mkdir()
            copy = case / 'packet'
            shutil.copytree(root, copy)
            target, used = copy, anchor
            if name == 'payload':
                with (copy / 'review.md').open('a') as f:
                    f.write('\nmutation\n')
            elif name == 'missing':
                (copy / 'identity-checks.json').unlink()
            elif name == 'extra_file':
                (copy / 'extra').write_text('x')
            elif name == 'extra_empty_directory':
                (copy / 'extra-empty').mkdir()
            elif name == 'root_symlink':
                target = case / 'link'
                target.symlink_to(copy, target_is_directory=True)
            elif name == 'ancestor_symlink':
                link = scratch / (name + '-ancestor')
                link.symlink_to(case, target_is_directory=True)
                target = link / 'packet'
            elif name == 'hardlink':
                outside = case / 'outside'
                shutil.copyfile(copy / 'review.md', outside)
                (copy / 'review.md').unlink()
                os.link(outside, copy / 'review.md')
            elif name == 'fifo':
                os.mkfifo(copy / 'pipe')
            elif name == 'nested_manifest':
                (copy / 'nested').mkdir()
                (copy / 'nested/manifest.json').write_text('{}')
            elif name == 'self_reseal':
                import hashlib
                p = copy / 'review.md'
                p.write_text(p.read_text() + '\nmutation\n')
                m = json.loads((copy / 'manifest.json').read_text())
                m['files']['review.md'] = {'bytes': p.stat().st_size, 'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
                (copy / 'manifest.json').write_text(json.dumps(m, indent=2, sort_keys=True) + '\n')
            elif name == 'wrong_anchor':
                used = '0' * 64
            result = run(target, used)
            cases[name] = result
            assert (result['returncode'] == 0) == (name == 'unchanged_copy'), (name, result)
        return {'status': 'PASS', 'anchor': anchor, 'cases': cases}
    finally:
        shutil.rmtree(scratch)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise SystemExit('usage: control-tests.py EXTERNAL_MANIFEST_SHA256')
    print(json.dumps(main(sys.argv[1]), indent=2))
