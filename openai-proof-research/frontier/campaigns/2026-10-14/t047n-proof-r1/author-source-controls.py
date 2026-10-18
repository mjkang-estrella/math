#!/usr/bin/env python3
"""Copied controls for the author verifier's --source-tree layer. MIT.
Works only on disposable copies of the frozen packet and of the tree file.

Usage: python3 -I author-source-controls.py PACKET TREE MANIFEST_SHA256 VERIFIER_SHA256
"""
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def reseal(c):
    m = json.loads((c / 'manifest.json').read_text())
    for sect in ('files', 'private_files'):
        for rel in m[sect]:
            f = c / rel
            m[sect][rel] = {'bytes': f.stat().st_size, 'sha256': sha(f)}
    (c / 'manifest.json').write_text(json.dumps(m, sort_keys=True, indent=2) + '\n')
    return sha(c / 'manifest.json')


def main():
    packet, tree, mh, vh = Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve(), sys.argv[3], sys.argv[4]
    results = {}
    with tempfile.TemporaryDirectory(prefix='t047n-srcctl-', dir='/var/tmp') as td:
        td = Path(td)
        cases = ['positive_source_tree', 'resealed_private_source_edit', 'tree_truncated_true',
                 'tree_extra_family_blob', 'tree_altered_family_sha', 'resealed_dropped_receipt',
                 'source_tree_with_public_only', 'resealed_proof_edit_old_anchor']
        for name in cases:
            c = td / name / 'packet'
            shutil.copytree(packet, c)
            t = td / name / 'tree.json'
            shutil.copyfile(tree, t)
            anchor = mh
            extra = []
            expect_ok = name == 'positive_source_tree'
            if name == 'resealed_private_source_edit':
                f = c / 'private/source047/06-rigidity.tex'
                f.write_text(f.read_text().replace('e\\le0', 'e\\ge0', 1))
                anchor = reseal(c)
            if name in ('tree_truncated_true', 'tree_extra_family_blob', 'tree_altered_family_sha'):
                d = json.loads(t.read_text())
                if name == 'tree_truncated_true':
                    d['truncated'] = True
                elif name == 'tree_extra_family_blob':
                    d['tree'].append({'path': 'preprints/An-explicit-failure-of-complex-affine-space-cancellation-September-23-2026/build/sections/08-extra.tex',
                                      'type': 'blob', 'sha': '0' * 40, 'mode': '100644'})
                else:
                    for x in d['tree']:
                        if x['path'].endswith('September-23-2026/build/sections/03-degeneration.tex'):
                            x['sha'] = '1' * 40
                t.write_text(json.dumps(d))
            if name == 'resealed_dropped_receipt':
                r = json.loads((c / 'source047-receipts.json').read_text())
                (c / 'source047-receipts.json').write_text(json.dumps(r[:-1], indent=2) + '\n')
                anchor = reseal(c)
            if name == 'source_tree_with_public_only':
                shutil.rmtree(c / 'private')
                extra = ['--public-only']
            if name == 'resealed_proof_edit_old_anchor':
                f = c / 'candidate-047.md'
                f.write_text(f.read_text().replace('(2−n)m−2<0', '(2−n)m−2<=0', 1))
                reseal(c)  # anchor intentionally left at the external value
            cmd = [sys.executable, '-I', str(c / 'verify.py'), '--expected-manifest', anchor,
                   '--expected-verifier', vh, '--source-tree', str(t), *extra]
            p = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
            ok = (p.returncode == 0) if expect_ok else (p.returncode != 0)
            if not ok:
                raise SystemExit('CONTROL FAILED ' + name + ': ' + p.stdout + p.stderr)
            results[name] = {'expected': 'accept' if expect_ok else 'reject', 'observed_exit': p.returncode,
                             'message': (p.stdout + p.stderr).strip()[:120]}
    print(json.dumps({'status': 'PASS_ALL_SOURCE_LAYER_CONTROLS', 'cases': results}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
