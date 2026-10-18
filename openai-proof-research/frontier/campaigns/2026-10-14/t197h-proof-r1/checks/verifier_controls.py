#!/usr/bin/env python3
"""MIT. Mutation controls for this directory's verify.py, on disposable copies only."""
import argparse, hashlib, importlib.util, json, os, shutil, tempfile
from pathlib import Path


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', type=Path, required=True)
    ap.add_argument('--scratch-parent', type=Path, default=Path('/var/tmp'))
    a = ap.parse_args()
    root = Path(os.path.abspath(a.root))
    scratch = Path(tempfile.mkdtemp(prefix='t197h-proof-r1-verifier-', dir=a.scratch_parent))
    results = []
    try:
        base = scratch / 'base'
        shutil.copytree(root, base, symlinks=True)
        sealed_input = (base / 'MANIFEST.json').exists()
        if not sealed_input:
            load(base / 'checks' / 'seal.py', 'seal_copy').seal(base)
        anchor = hashlib.sha256((base / 'MANIFEST.json').read_bytes()).hexdigest()
        v = load(base / 'verify.py', 'verify_copy')

        def run(name, mutate=None, wrong=False, via=None, expect=False):
            d = scratch / name
            shutil.copytree(base, d, symlinks=True)
            target = d
            if mutate:
                r = mutate(d)
                if isinstance(r, Path):
                    target = r
            try:
                v.check(target, '0' * 64 if wrong else anchor)
                ok, why = True, 'PASS'
            except Exception as e:  # noqa: BLE001
                ok, why = False, str(e)
            assert ok == expect, (name, ok, why)
            results.append({'case': name, 'expected': 'accept' if expect else 'reject', 'actual': why})

        run('positive_copy', expect=True)
        run('wrong_anchor', wrong=True)
        run('changed_review', lambda d: (d / 'review.md').write_bytes((d / 'review.md').read_bytes() + b'x'))
        run('missing_payload', lambda d: (d / 'read-limits.md').unlink())
        run('extra_file', lambda d: (d / 'extra.txt').write_text('x'))
        run('extra_empty_directory', lambda d: (d / 'extra-dir').mkdir())

        def rootlink(d):
            link = scratch / 'root-link'
            link.symlink_to(d, target_is_directory=True)
            return link
        run('root_symlink', rootlink)

        def ancestorlink(d):
            link = scratch / 'ancestor-link'
            link.symlink_to(scratch, target_is_directory=True)
            return link / d.name
        run('ancestor_symlink', ancestorlink)

        def payloadlink(d):
            (d / 'README.md').unlink()
            (d / 'README.md').symlink_to('review.md')
        run('payload_symlink', payloadlink)

        def hardlink(d):
            (d / 'README.md').unlink()
            os.link(d / 'review.md', d / 'README.md')
        run('payload_hardlink', hardlink)
        run('fifo', lambda d: os.mkfifo(d / 'fifo'))

        def reseal(d):
            f = d / 'status.json'
            f.write_text(f.read_text().replace('PASS_FULL_T197H', 'FAIL'))
            load(d / 'checks' / 'seal.py', 'seal_mut').seal(d)
        run('self_resealed_wrong_external_anchor', reseal)
    finally:
        shutil.rmtree(scratch)
    print(json.dumps({'status': 'PASS', 'input_was_sealed': sealed_input, 'controls': results,
                      'scope': 'Copied-packet controls for verify.py only; no mathematical claim.'}, indent=2))


if __name__ == '__main__':
    main()
