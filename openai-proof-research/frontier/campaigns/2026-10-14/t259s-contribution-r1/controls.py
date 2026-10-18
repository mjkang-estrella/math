#!/usr/bin/env python3
"""Copied adversarial controls for the T259S contribution review r1 seal. MIT.

Never modifies the invoking packet or the author packet. Every mutation is applied to a
fresh copy under --workdir, which must lie outside both packets and must not yet exist.
"""
import argparse, json, os, shutil, subprocess, sys
from pathlib import Path


def run(cmd):
    return subprocess.run(cmd, capture_output=True, text=True, timeout=120)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--expected-manifest', required=True); ap.add_argument('--expected-verifier', required=True)
    ap.add_argument('--workdir', required=True); ap.add_argument('--author-packet', required=True)
    ap.add_argument('--source-tree', required=True)
    a = ap.parse_args()
    root = Path(os.path.abspath(__file__)).parent
    author = Path(os.path.abspath(a.author_packet)); tree = Path(os.path.abspath(a.source_tree))
    wd = Path(os.path.abspath(a.workdir))
    for p in (root, author):
        if wd == p or p in wd.parents:
            sys.exit('workdir must lie outside the tested packets')
    wd.mkdir(parents=True)
    mh, vh = a.expected_manifest, a.expected_verifier
    results = {}
    cases = ['positive', 'author_positive', 'wrong_manifest', 'wrong_verifier', 'edit_review', 'delete_review',
             'extra_file', 'extra_empty_dir', 'nested_manifest', 'root_symlink', 'ancestor_symlink', 'hardlink',
             'fifo', 'edit_manifest', 'edit_verifier', 'self_reseal', 'author_source_edit', 'author_candidate_edit',
             'author_extra_source', 'tree_altered', 'tree_truncated', 'half_source_flags']
    for name in cases:
        case = wd / name; case.mkdir()
        c = case / 'packet'; shutil.copytree(root, c)
        invoke, m, v, extra = c, mh, vh, []
        if name in ('author_positive', 'author_source_edit', 'author_candidate_edit', 'author_extra_source',
                    'tree_altered', 'tree_truncated'):
            ac = case / 'author'; shutil.copytree(author, ac); t = tree
            src = ac / 'private/preprints/A-group-without-fixed-price-October-5-2026/build/group-actions.tex'
            if name == 'author_source_edit':
                src.write_bytes(src.read_bytes() + b'%\n')
            if name == 'author_candidate_edit':
                with (ac / 'candidate-259.md').open('a') as f:
                    f.write('\n')
            if name == 'author_extra_source':
                (src.parent / 'extra.tex').write_text('x')
            if name == 'tree_altered':
                t = case / 'tree.json'; t.write_bytes(tree.read_bytes() + b'\n')
            if name == 'tree_truncated':
                t = case / 'tree.json'; d = json.loads(tree.read_text()); d['truncated'] = True; t.write_text(json.dumps(d))
            extra = ['--author-packet', str(ac), '--source-tree', str(t)]
        if name == 'half_source_flags':
            extra = ['--source-tree', str(tree)]
        if name == 'wrong_manifest': m = '0' * 64
        if name == 'wrong_verifier': v = '0' * 64
        if name == 'edit_review':
            with (c / 'review.md').open('a') as f: f.write('\nmutation\n')
        if name == 'delete_review': (c / 'review.md').unlink()
        if name == 'extra_file': (c / 'extra.txt').write_text('x')
        if name == 'extra_empty_dir': (c / 'empty').mkdir()
        if name == 'nested_manifest': (c / 'n').mkdir(); (c / 'n/manifest.json').write_text('{}')
        if name == 'root_symlink':
            invoke = case / 'link'; invoke.symlink_to(c, target_is_directory=True)
        if name == 'ancestor_symlink':
            (case / 'holder').mkdir(); shutil.move(str(c), str(case / 'holder/packet'))
            (case / 'hl').symlink_to(case / 'holder', target_is_directory=True); invoke = case / 'hl/packet'
        if name == 'hardlink': os.link(c / 'review.md', c / 'review-hardlink.md')
        if name == 'fifo': os.mkfifo(c / 'fifo')
        if name == 'edit_manifest':
            with (c / 'manifest.json').open('a') as f: f.write(' ')
        if name == 'edit_verifier':
            with (c / 'verify.py').open('a') as f: f.write('\n# mutation\n')
        if name == 'self_reseal':
            import hashlib
            p = c / 'review.md'; p.write_text(p.read_text() + '\nmutation\n')
            mm = json.loads((c / 'manifest.json').read_text())
            mm['files']['review.md'] = {'bytes': p.stat().st_size, 'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
            (c / 'manifest.json').write_text(json.dumps(mm, sort_keys=True, indent=2) + '\n')
        r = run([sys.executable, str(invoke / 'verify.py'), '--expected-manifest', m, '--expected-verifier', v, *extra])
        ok = (r.returncode == 0) if name in ('positive', 'author_positive') else (r.returncode != 0)
        if not ok:
            raise AssertionError(name + ': ' + r.stdout + r.stderr)
        results[name] = 'PASS (' + (r.stdout.strip() if r.returncode == 0 else r.stderr.strip()) + ')'
    shutil.rmtree(wd)
    print(json.dumps({'status': 'PASS_ALL_COPIED_CONTROLS', 'cases': results}, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
