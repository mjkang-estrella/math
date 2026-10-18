#!/usr/bin/env python3
"""MIT. Reason-checked negative controls for verify.py, run only on copies.

Usage: python3 controls.py <external manifest SHA256> <fresh scratch dir under /var/tmp>

Copies sources/{preprints-tree.json,upstream.json}, this review directory and the
frozen r53 packet into a scratch replica, mutates only the replica, and requires
each control to fail with its expected reason. Originals are only read.
"""
import json, os, shutil, subprocess, sys
from pathlib import Path

REL = Path('frontier/campaigns/2026-10-14')
R53 = 'fresh-arithmetic-discovery-r53'


def replica(src_repo, review_name, dst):
    if dst.exists():
        raise SystemExit('scratch replica already exists: ' + str(dst))
    (dst / 'sources').mkdir(parents=True)
    for n in ('preprints-tree.json', 'upstream.json'):
        shutil.copy2(src_repo / 'sources' / n, dst / 'sources' / n)
    for n in (review_name, R53):
        shutil.copytree(src_repo / REL / n, dst / REL / n, symlinks=True)
    return dst / REL / review_name


def run(review, args):
    p = subprocess.run([sys.executable, str(review / 'verify.py'), *args],
                       capture_output=True, text=True)
    return p.returncode, p.stdout.strip(), p.stderr.strip()


def main():
    if len(sys.argv) != 3 or not sys.argv[2].startswith('/var/tmp/'):
        raise SystemExit('usage: controls.py <anchor> </var/tmp/scratch>')
    anchor, scratch = sys.argv[1], Path(sys.argv[2])
    here = Path(os.path.abspath(__file__)).parent
    src_repo = here.parents[3]

    def flip(p):
        b = bytearray(p.read_bytes()); b[len(b) // 2] ^= 1; p.write_bytes(bytes(b))

    controls = [
        ('C00_baseline', None, [anchor], 0, 'PASS_EXACT_INVENTORY'),
        ('C01_missing_anchor', None, [], 1, 'external SHA256 argument required'),
        ('C02_wrong_anchor', None, ['0' * 64], 1, 'external manifest anchor mismatch'),
        ('C03_report_byte_flip', lambda r: flip(r / 'report.md'), [anchor], 1, 'file inventory mismatch'),
        ('C04_extra_review_file', lambda r: (r / 'extra.txt').write_text('x'), [anchor], 1, 'file inventory mismatch'),
        ('C05_symlink_in_review', lambda r: os.symlink('report.md', r / 'link.md'), [anchor], 1, 'nonregular entry'),
        ('C06_hardlink_in_review', lambda r: os.link(r / 'report.md', r / 'hl.md'), [anchor], 1, 'hardlink'),
        ('C07_r53_candidate_flip', lambda r: flip(r.parent / R53 / 'candidate-proof.md'), [anchor], 1, 'frozen r53 anchor mismatch'),
        ('C08_r53_source_blob_flip', lambda r: flip(r.parent / R53 / 'private/source024/build/source/layers.tex'), [anchor], 1, 'source blob identity mismatch'),
        ('C09_r53_extra_private_file', lambda r: (r.parent / R53 / 'private/extra.txt').write_text('x'), [anchor], 1, 'r53 inventory mismatch'),
        ('C10_tree_flip', lambda r: flip(r.parents[3] / 'sources/preprints-tree.json'), [anchor], 1, 'canonical tree mismatch'),
        ('C11_nested_manifest', lambda r: (r / 'sub').mkdir() or (r / 'sub/manifest.json').write_text('{}'), [anchor], 1, 'nested manifest'),
    ]
    results, ok = [], True
    for name, mutate, args, want_rc, reason in controls:
        review = replica(src_repo, here.name, scratch / name)
        if mutate:
            mutate(review)
        rc, out, err = run(review, args)
        passed = rc == want_rc and reason in (out if want_rc == 0 else err)
        ok &= passed
        results.append({'control': name, 'rc': rc, 'expected_reason': reason,
                        'observed': out if want_rc == 0 else err, 'reason_checked': passed})
    print(json.dumps({'all_controls_reason_checked': ok, 'controls': results}, indent=1))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
