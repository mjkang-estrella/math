#!/usr/bin/env python3
"""Run final integrity controls on disposable copies, never on the original packet."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys

def sha(b):
    return hashlib.sha256(b).hexdigest()

def snapshot(root, excluded=None):
    result = {}
    for p in [root] + sorted(root.rglob('*')):
        if excluded is not None and (p == excluded or excluded in p.parents):
            continue
        s = p.lstat()
        row = {'mode': s.st_mode}
        if stat.S_ISREG(s.st_mode):
            row['links'] = s.st_nlink
            row['sha256'] = sha(p.read_bytes())
        elif stat.S_ISLNK(s.st_mode):
            row['target'] = os.readlink(p)
        result[p.relative_to(root).as_posix()] = row
    return result

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('root', type=Path)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--finalhash', required=True)
    ap.add_argument('--reporthash', required=True)
    ap.add_argument('--tree', type=Path, required=True)
    a = ap.parse_args()
    root, out = a.root.absolute(), a.out.absolute()
    if out.exists() or root not in out.parents or out == root / 'packet' or root / 'packet' in out.parents:
        raise ValueError('output must be a fresh owned directory outside packet')
    # Parent directories must already exist so excluding out omits only new output.
    if not out.parent.is_dir():
        raise ValueError('output parent must already exist')
    before = snapshot(root, out)
    out.mkdir()
    cases = ['baseline', 'wrong-final', 'wrong-report', 'changed-payload', 'missing-payload', 'extra-payload', 'extra-directory', 'changed-file-mode', 'changed-directory-mode', 'symlink', 'hardlink', 'fifo', 'changed-manifest', 'changed-final', 'changed-source', 'changed-primary', 'changed-history', 'changed-verifier', 'wrong-tree', 'coherent-reseal', 'write-denial-probe', 'process-denial-probe']
    receipt = []
    for case in cases:
        c = out / case
        c.mkdir()
        shutil.copytree(root / 'packet', c / 'packet')
        for name in ('MANIFEST.json', 'FINAL.json'):
            shutil.copy2(root / name, c / name)
        target = c / 'packet/public/report.md'
        finalhash, reporthash, tree = a.finalhash, a.reporthash, a.tree.absolute()
        if case == 'wrong-final': finalhash = '0' * 64
        elif case == 'wrong-report': reporthash = '0' * 64
        elif case == 'changed-payload': target.write_bytes(target.read_bytes() + b'\nchanged\n')
        elif case == 'missing-payload': target.unlink()
        elif case == 'extra-payload': (c / 'packet/extra.txt').write_text('extra')
        elif case == 'extra-directory': (c / 'packet/extra-empty').mkdir()
        elif case == 'changed-file-mode': target.chmod(0o600)
        elif case == 'changed-directory-mode': (c / 'packet/public').chmod(0o700)
        elif case == 'symlink':
            target.unlink(); target.symlink_to(c / 'FINAL.json')
        elif case == 'hardlink':
            target.unlink(); os.link(c / 'packet/public/nls-geometry.md', target)
        elif case == 'fifo':
            target.unlink(); os.mkfifo(target)
        elif case == 'changed-manifest': (c / 'MANIFEST.json').write_text('{}\n')
        elif case == 'changed-final': (c / 'FINAL.json').write_text('{}\n')
        elif case in ('changed-source', 'changed-primary', 'changed-history'):
            folder = {'changed-source': 'sources', 'changed-primary': 'primary', 'changed-history': 'history'}[case]
            p = next(x for x in sorted((c / 'packet/private' / folder).iterdir()) if x.is_file())
            p.write_bytes(p.read_bytes() + b'changed')
        elif case == 'changed-verifier':
            p = c / 'packet/public/verify.py'; p.write_bytes(p.read_bytes() + b'\n# changed\n')
        elif case == 'wrong-tree':
            tree = c / 'wrong-tree.json'; tree.write_text('{"truncated": true, "tree": []}\n')
        elif case == 'coherent-reseal':
            target.write_bytes(target.read_bytes() + b'\nchanged\n')
            m = json.loads((c / 'MANIFEST.json').read_text())
            m['files']['public/report.md']['sha256'] = sha(target.read_bytes())
            m['files']['public/report.md']['bytes'] = target.stat().st_size
            (c / 'MANIFEST.json').write_text(json.dumps(m, sort_keys=True) + '\n')
            f = json.loads((c / 'FINAL.json').read_text())
            f['manifest_sha256'] = sha((c / 'MANIFEST.json').read_bytes())
            f['report_sha256'] = sha(target.read_bytes())
            (c / 'FINAL.json').write_text(json.dumps(f, sort_keys=True) + '\n')
        elif case.endswith('denial-probe'):
            p = c / 'packet/public/verify.py'
            probe = "open('R122_FORBIDDEN_WRITE', 'w')" if case == 'write-denial-probe' else "os.system('true')"
            p.write_text(p.read_text().replace('sys.addaudithook(guard)', 'sys.addaudithook(guard)\n' + probe, 1))
        state = snapshot(c)
        command = [sys.executable, '-B', str(c / 'packet/public/verify.py'), str(c), '--finalhash', finalhash, '--reporthash', reporthash, '--tree', str(tree)]
        z = subprocess.run(command, capture_output=True, text=True, cwd=c, timeout=45)
        unchanged = state == snapshot(c)
        expected = z.returncode == 0 if case == 'baseline' else z.returncode != 0
        if case.endswith('denial-probe'):
            expected = expected and 'verifier denies' in z.stderr
        row = {'case': case, 'returncode': z.returncode, 'expected_outcome': expected, 'copy_unchanged_by_verifier': unchanged, 'stdout': z.stdout, 'stderr': z.stderr}
        receipt.append(row)
        if not expected or not unchanged:
            raise RuntimeError(json.dumps(row))
        shutil.rmtree(c)
    original_unchanged = before == snapshot(root, out)
    if not original_unchanged:
        raise RuntimeError('original preexisting tree changed')
    result = {'mathematical_gate': False, 'cases': receipt, 'all_expected': True, 'original_preexisting_tree_unchanged': True, 'excluded_new_output_only': str(out), 'final_sha256': a.finalhash, 'report_sha256': a.reporthash}
    (out / 'receipt.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'all_expected': True, 'cases': len(receipt), 'original_preexisting_tree_unchanged': True, 'receipt': str(out / 'receipt.json')}))

if __name__ == '__main__':
    main()
