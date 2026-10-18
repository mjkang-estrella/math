#!/usr/bin/env python3
"""MIT. Mutation controls for this review's verifier, on disposable /var/tmp copies only.

Usage: own_controls.py EXTERNAL_MANIFEST_SHA256
Never writes inside the sealed review directory; prints JSON to stdout.
"""
import json, os, shutil, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def run(target, anchor):
    c = subprocess.run([sys.executable, '-B', str(target / 'verify.py'), '--expected-manifest-sha256', anchor],
                       capture_output=True, text=True)
    return {'returncode': c.returncode, 'output': (c.stdout + c.stderr).strip()}


def main(anchor):
    scratch = Path(tempfile.mkdtemp(prefix='t250p-contrib-own-', dir='/var/tmp'))
    cases = {}
    try:
        cases['sealed_original'] = run(ROOT, anchor)
        names = ['unchanged_copy', 'wrong_anchor_zero', 'wrong_anchor_flip', 'review_payload', 'record_payload',
                 'missing_file', 'extra_file', 'extra_empty_directory', 'root_symlink', 'ancestor_symlink',
                 'hardlink', 'fifo', 'nested_manifest', 'self_reseal', 'verdict_swap_resealed']
        for name in names:
            case = scratch / name
            case.mkdir()
            copy = case / 'review'
            shutil.copytree(ROOT, copy, ignore=shutil.ignore_patterns('__pycache__'))
            target, used = copy, anchor
            if name == 'wrong_anchor_zero':
                used = '0' * 64
            elif name == 'wrong_anchor_flip':
                used = anchor[:-1] + ('0' if anchor[-1] != '0' else '1')
            elif name == 'review_payload':
                with (copy / 'review.md').open('a') as f:
                    f.write('\nmutation\n')
            elif name == 'record_payload':
                p = copy / 'records/canonical-compare.json'
                p.write_bytes(p.read_bytes().replace(b'PASS', b'FAIL', 1))
            elif name == 'missing_file':
                (copy / 'README.md').unlink()
            elif name == 'extra_file':
                (copy / 'extra.txt').write_text('x')
            elif name == 'extra_empty_directory':
                (copy / 'extra-empty').mkdir()
            elif name == 'root_symlink':
                target = case / 'link'
                target.symlink_to(copy, target_is_directory=True)
            elif name == 'ancestor_symlink':
                link = scratch / (name + '-ancestor')
                link.symlink_to(case, target_is_directory=True)
                target = link / 'review'
            elif name == 'hardlink':
                outside = case / 'outside'
                shutil.copyfile(copy / 'README.md', outside)
                (copy / 'README.md').unlink()
                os.link(outside, copy / 'README.md')
            elif name == 'fifo':
                os.mkfifo(copy / 'pipe')
            elif name == 'nested_manifest':
                (copy / 'records/MANIFEST.json').write_text('{}')
            elif name in ('self_reseal', 'verdict_swap_resealed'):
                p = copy / 'review.md'
                text = p.read_text()
                text = text.replace('**TECHNICAL**', '**SUBSTANTIAL**') if name == 'verdict_swap_resealed' \
                    else text + '\nmutation\n'
                p.write_text(text)
                m = json.loads((copy / 'MANIFEST.json').read_text())
                import hashlib
                for e in m['files']:
                    if e['path'] == 'review.md':
                        b = p.read_bytes()
                        e['bytes'] = len(b)
                        e['sha256'] = hashlib.sha256(b).hexdigest()
                (copy / 'MANIFEST.json').write_text(json.dumps(m, indent=2, sort_keys=True) + '\n')
            result = run(target, used)
            cases[name] = result
            expect_pass = name == 'unchanged_copy'
            assert (result['returncode'] == 0) == expect_pass, (name, result)
        assert cases['sealed_original']['returncode'] == 0, cases['sealed_original']
        return {'status': 'PASS', 'anchor': anchor, 'cases': cases,
                'note': 'Identity/rejection behaviour only; scratch under /var/tmp removed afterwards.'}
    finally:
        shutil.rmtree(scratch)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise SystemExit('usage: own_controls.py EXTERNAL_MANIFEST_SHA256')
    print(json.dumps(main(sys.argv[1]), indent=2, sort_keys=True))
