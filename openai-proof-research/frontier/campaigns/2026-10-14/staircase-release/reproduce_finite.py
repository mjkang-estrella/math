#!/usr/bin/env python3
"""Run frozen finite programs on disposable copies. Myeongjin Kang 2026; MIT."""
import argparse
from pathlib import Path
import subprocess
import sys
import tempfile
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import release_common as c


def reproduce(root):
    rows = c.frozen_selection(root)
    with tempfile.TemporaryDirectory(prefix='.finite-copy-', dir=c.HERE) as d:
        temp = Path(d)
        for path in rows:
            if path.startswith(c.PAPER + '/'):
                target = temp / path[len(c.PAPER)+1:]
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(c.selected(root, path))
        old = c.decode((temp / 'checks/reproduction.json').read_bytes())
        proc = subprocess.run([sys.executable, '-I', str(temp / 'support/reproduce.py')],
                              cwd=temp, capture_output=True, text=True, timeout=180)
        c.require(proc.returncode == 0, 'Finite controls failed: ' + proc.stderr)
        fresh = c.decode((temp / 'checks/reproduction.json').read_bytes())
        # Interpreter patch version can differ; all mathematical records must match.
        c.require({k:v for k,v in fresh.items() if k != 'python'} ==
                  {k:v for k,v in old.items() if k != 'python'}, 'Finite receipt differs')
        return {'status': 'PASS', 'result': proc.stdout.strip(),
                'programs': fresh['runs'], 'interface_control': fresh['interface_control'],
                'receipt_comparison': 'Every field except interpreter version equal',
                'finite_only': True, 'writes': 'Disposable copy only; removed'}


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', type=Path, default=c.ROOT)
    a = p.parse_args()
    print(c.encode(reproduce(a.root)).decode(), end='')
