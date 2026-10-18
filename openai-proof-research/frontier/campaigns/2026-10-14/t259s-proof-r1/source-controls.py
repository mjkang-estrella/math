#!/usr/bin/env python3
"""Reviewer-owned source-authentication controls on disposable copies. MIT.

Each case copies the frozen author packet into SCRATCH (never the original),
applies one change, and runs the copied author verify.py with --source-tree.
Resealed cases rewrite the COPY's manifest and pass its new hash as the
anchor, so the source-identity branch itself (not only the inventory hash)
is exercised. Exits nonzero unless positive cases pass and all others fail.
"""
import argparse, hashlib, json, shutil, subprocess, sys
from pathlib import Path

FAM = 'A-group-without-fixed-price-October-5-2026'


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def git_blob(b):
    return hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()


def reseal(c):
    m = json.loads((c / 'manifest.json').read_text())
    for key in ('files', 'private_files'):
        for rel in list(m[key]):
            p = c / rel
            if p.exists():
                m[key][rel] = {'bytes': p.stat().st_size, 'sha256': sha(p)}
            else:
                del m[key][rel]
    (c / 'manifest.json').write_text(json.dumps(m, sort_keys=True, indent=2) + '\n')
    return sha(c / 'manifest.json')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--packet', required=True)
    ap.add_argument('--scratch', required=True)
    ap.add_argument('--source-tree', required=True)
    ap.add_argument('--truncated-tree', required=True)
    ap.add_argument('--expected-manifest', required=True)
    ap.add_argument('--expected-verifier', required=True)
    a = ap.parse_args()
    src = Path(a.packet)
    scratch = Path(a.scratch)
    tree = Path(a.source_tree)
    results = {}
    cases = ['positive', 'truncated_tree', 'mutated_tree_copy', 'edit_source_no_reseal',
             'edit_source_resealed', 'edit_source_and_receipt_resealed',
             'delete_source_and_receipt_resealed', 'public_only_with_tree']
    for name in cases:
        c = scratch / 'copy'
        if c.exists():
            shutil.rmtree(c)
        shutil.copytree(src, c, symlinks=True)
        mh, tr, extra = a.expected_manifest, str(tree), []
        target = c / 'private/preprints' / FAM / 'build/introduction.tex'
        if name == 'truncated_tree':
            tr = a.truncated_tree
        if name == 'mutated_tree_copy':
            t = json.loads(tree.read_text())
            for e in t['tree']:
                if e['path'].endswith(FAM + '/build/introduction.tex'):
                    e['sha'] = '0' * 40
            mt = scratch / 'mutated-tree.json'
            mt.write_text(json.dumps(t))
            tr = str(mt)
        if name.startswith('edit_source'):
            target.write_bytes(target.read_bytes().replace(b'\\ge1+\\eta', b'\\ge1+2\\eta', 1))
        if name == 'edit_source_and_receipt_resealed':
            rp = c / 'source259-receipts.json'
            rec = json.loads(rp.read_text())
            b = target.read_bytes()
            for r in rec:
                if r['source_path'].endswith('build/introduction.tex'):
                    r.update({'git_blob': git_blob(b), 'sha256': hashlib.sha256(b).hexdigest(), 'bytes': len(b)})
            rp.write_text(json.dumps(rec, indent=2) + '\n')
        if name == 'delete_source_and_receipt_resealed':
            target.unlink()
            rp = c / 'source259-receipts.json'
            rec = [r for r in json.loads(rp.read_text()) if not r['source_path'].endswith('build/introduction.tex')]
            rp.write_text(json.dumps(rec, indent=2) + '\n')
        if name in ('edit_source_resealed', 'edit_source_and_receipt_resealed', 'delete_source_and_receipt_resealed'):
            mh = reseal(c)
        if name == 'public_only_with_tree':
            shutil.rmtree(c / 'private')
            extra = ['--public-only']
        cmd = [sys.executable, str(c / 'verify.py'), '--expected-manifest', mh,
               '--expected-verifier', a.expected_verifier, '--source-tree', tr, *extra]
        run = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
        ok = run.returncode == 0 if name == 'positive' else run.returncode != 0
        results[name] = {'expected': 'pass' if name == 'positive' else 'fail',
                         'returncode': run.returncode,
                         'output': (run.stdout + run.stderr).strip()[:200],
                         'control': 'PASS' if ok else 'FAILED'}
        shutil.rmtree(c)
    mt = scratch / 'mutated-tree.json'
    if mt.exists():
        mt.unlink()
    status = 'PASS_ALL_SOURCE_CONTROLS' if all(r['control'] == 'PASS' for r in results.values()) else 'CONTROL_FAILURE'
    print(json.dumps({'status': status, 'cases': results}, sort_keys=True, indent=2))
    sys.exit(0 if status.startswith('PASS') else 1)


if __name__ == '__main__':
    main()
