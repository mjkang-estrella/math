#!/usr/bin/env python3
"""Exercise the original verifier on disposable copies; integrity only."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile


def digest(b):
    return hashlib.sha256(b).hexdigest()


def dump(p, obj):
    p.write_text(json.dumps(obj, indent=2, sort_keys=True) + '\n')


def inventory(p):
    fs, ds = [], []
    for x in sorted(p.rglob('*')):
        s = x.relative_to(p).as_posix()
        st = x.lstat()
        if stat.S_ISDIR(st.st_mode):
            ds.append(s)
        elif stat.S_ISREG(st.st_mode):
            b = x.read_bytes()
            fs.append({'path': s, 'bytes': len(b), 'sha256': digest(b), 'mode': stat.S_IMODE(st.st_mode)})
        else:
            raise RuntimeError('unexpected nonregular path in reseal')
    return {'schema': 'r122-manifest-v1', 'files': fs, 'directories': ds}


def reseal_for_control(root):
    # Control copies ONLY. This function is not the read-only verifier.
    dump(root / 'MANIFEST.json', inventory(root / 'packet'))
    f = json.loads((root / 'FINAL.json').read_text())
    f['manifest_sha256'] = digest((root / 'MANIFEST.json').read_bytes())
    dump(root / 'FINAL.json', f)
    return digest((root / 'FINAL.json').read_bytes())


def protected(root):
    result = []
    for x in sorted(root.rglob('*')):
        rel = x.relative_to(root)
        if rel.parts[0] == 'controls':
            continue
        st = x.lstat()
        record = [rel.as_posix(), stat.S_IFMT(st.st_mode), stat.S_IMODE(st.st_mode), st.st_nlink]
        if x.is_file():
            record += [len(x.read_bytes()), digest(x.read_bytes())]
        result.append(record)
    return digest(json.dumps(result, sort_keys=True).encode())


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True, type=Path)
    ap.add_argument('--tree', required=True, type=Path)
    ap.add_argument('--finalhash', required=True)
    ap.add_argument('--reporthash', required=True)
    a = ap.parse_args()
    root = a.root.absolute()
    own = Path(__file__).absolute().parents[2]
    if own != root:
        raise RuntimeError('runner root must be its own assigned archive')
    out = root / 'controls'
    out.mkdir(exist_ok=True)
    before = protected(root)
    verifier = root / 'packet/public/verify.py'
    cases = [('baseline', ''), ('wrong-final', 'detached FINAL'),
             ('missing-final', '--finalhash'), ('wrong-report', 'detached report'),
             ('edit-report', 'detached report'), ('edit-payload', 'payload bytes'),
             ('extra-file', 'file membership'), ('missing-file', 'file membership'),
             ('extra-directory', 'directory membership'), ('symlink-payload', 'symlink payload'),
             ('hardlink-payload', 'hardlinked payload'), ('fifo-payload', 'nonregular payload'),
             ('edit-manifest', 'manifest hash'), ('coherent-reseal-old-anchor', 'detached FINAL'),
             ('source-blob-new-test-anchor', 'source Git blob'),
             ('source-url-new-test-anchor', 'source raw URL'),
             ('primary-new-test-anchor', 'primary bytes/hash'),
             ('selection-new-test-anchor', 'canonical selection'),
             ('unsafe-manifest-new-test-anchor', 'unsafe manifest path'),
             ('wrong-tree', 'canonical tree hash'), ('truncated-tree', 'canonical tree hash'),
             ('edit-verifier-payload', 'payload bytes'), ('symlink-root', 'symlink path')]
    results = []
    for name, expected in cases:
        with tempfile.TemporaryDirectory(prefix='copy-', dir=out) as td:
            base = Path(td)
            copy = base / 'archive'
            copy.mkdir()
            shutil.copytree(root / 'packet', copy / 'packet')
            for fn in ['FINAL.json', 'MANIFEST.json', 'REPORT.md']:
                shutil.copy2(root / fn, copy / fn)
            p = copy / 'packet'
            target = p / 'public/hypergraph-feasibility.md'
            finalhash, reporthash, tree, invoke_root = a.finalhash, a.reporthash, a.tree, copy
            if name == 'wrong-final': finalhash = '0' * 64
            elif name == 'wrong-report': reporthash = '0' * 64
            elif name == 'edit-report': (copy / 'REPORT.md').write_text('altered\n')
            elif name == 'edit-payload': target.write_bytes(target.read_bytes() + b'altered\n')
            elif name == 'extra-file': (p / 'extra.txt').write_text('extra\n')
            elif name == 'missing-file': target.unlink()
            elif name == 'extra-directory': (p / 'empty-extra').mkdir()
            elif name == 'symlink-payload':
                target.unlink(); target.symlink_to('/dev/null')
            elif name == 'hardlink-payload': os.link(target, base / 'second-link')
            elif name == 'fifo-payload':
                target.unlink(); os.mkfifo(target)
            elif name == 'edit-manifest':
                with (copy / 'MANIFEST.json').open('a') as f: f.write(' ')
            elif name == 'coherent-reseal-old-anchor':
                target.write_bytes(target.read_bytes() + b'altered\n'); reseal_for_control(copy)
            elif name == 'source-blob-new-test-anchor':
                sr = json.loads((p / 'public/source-register.json').read_text())
                r = sr[0]; q = p / r['path']; q.write_bytes(q.read_bytes() + b'\n% changed\n')
                for rec in [r]:
                    rec['sha256'] = digest(q.read_bytes()); rec['bytes'] = len(q.read_bytes())
                dump(p / 'public/source-register.json', sr)
                finalhash = reseal_for_control(copy)
            elif name == 'source-url-new-test-anchor':
                for fn in ['source-register.json']:
                    reg = json.loads((p / 'public' / fn).read_text())
                    reg[0]['raw_url'] = 'https://example.invalid/unpinned'
                    dump(p / 'public' / fn, reg)
                finalhash = reseal_for_control(copy)
            elif name == 'primary-new-test-anchor':
                reg = json.loads((p / 'public/primary-register.json').read_text())
                q = p / reg[0]['text']; q.write_bytes(q.read_bytes() + b'altered')
                finalhash = reseal_for_control(copy)
            elif name == 'selection-new-test-anchor':
                q = p / 'public/canonical-selection.json'; reg = json.loads(q.read_text()); reg[0]['mode'] = '100755'; dump(q, reg)
                finalhash = reseal_for_control(copy)
            elif name == 'unsafe-manifest-new-test-anchor':
                m = json.loads((copy / 'MANIFEST.json').read_text()); m['files'][0]['path'] = '../escape'
                dump(copy / 'MANIFEST.json', m)
                f = json.loads((copy / 'FINAL.json').read_text()); f['manifest_sha256'] = digest((copy / 'MANIFEST.json').read_bytes())
                dump(copy / 'FINAL.json', f); finalhash = digest((copy / 'FINAL.json').read_bytes())
            elif name in ['wrong-tree', 'truncated-tree']:
                tree = base / 'tree.json'
                if name == 'wrong-tree': tree.write_bytes(a.tree.read_bytes() + b' ')
                else:
                    t = json.loads(a.tree.read_text()); t['truncated'] = True; dump(tree, t)
            elif name == 'edit-verifier-payload':
                q = p / 'public/verify.py'; q.write_bytes(q.read_bytes() + b'\n# altered\n')
            elif name == 'symlink-root':
                invoke_root = base / 'symlink-archive'; invoke_root.symlink_to(copy, target_is_directory=True)
            cmd = [sys.executable, '-B', str(verifier), '--root', str(invoke_root), '--tree', str(tree), '--reporthash', reporthash]
            if name != 'missing-final': cmd += ['--finalhash', finalhash]
            run = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
            transcript = run.stdout + run.stderr
            matched = (run.returncode == 0 if name == 'baseline' else run.returncode != 0 and expected in transcript)
            results.append({'case': name, 'expected_substring': expected, 'returncode': run.returncode,
                            'matched': matched, 'stdout': run.stdout, 'stderr': run.stderr,
                            'new_test_anchor': 'new-test-anchor' in name})
    after = protected(root)
    obj = {'scope': 'INTEGRITY_ONLY_NOT_MATHEMATICAL_GATES', 'final_sha256': a.finalhash,
           'report_sha256': a.reporthash, 'cases': results, 'all_expected': all(x['matched'] for x in results),
           'protected_before': before, 'protected_after': after, 'original_unchanged': before == after,
           'temporary_copies_removed': True,
           'tree_control_limit': 'Wrong/truncated tree rejected by fixed SHA256 before parser; no isolated parser test claimed.'}
    dump(out / 'integrity-controls.json', obj)
    print(json.dumps({'cases': len(results), 'all_expected': obj['all_expected'], 'original_unchanged': before == after}))
    if not obj['all_expected'] or before != after:
        sys.exit(1)


if __name__ == '__main__':
    main()
