#!/usr/bin/env python3
"""Build the T298P manuscript in a fresh output directory. MIT, Myeongjin Kang."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

HERE = Path(__file__).resolve().parent

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, required=True, help='Fresh build directory')
    p.add_argument('--tectonic', type=Path, default=Path('/tmp/frontier-typeset/tectonic'))
    a = p.parse_args()
    out = a.output.absolute()
    out.mkdir(parents=True, exist_ok=False)
    shutil.copyfile(HERE / 'main.tex', out / 'main.tex')
    env = os.environ.copy()
    env['SOURCE_DATE_EPOCH'] = '1792281600'
    version = subprocess.check_output([str(a.tectonic), '--version'], text=True).strip()
    run = subprocess.run([str(a.tectonic), '--keep-logs', 'main.tex'], cwd=out,
                         env=env, text=True, capture_output=True)
    (out / 'build-console.log').write_text(run.stdout + run.stderr)
    receipt = {'role': 'author-side typesetting, not mathematical validation',
               'source_sha256': sha(HERE / 'main.tex'), 'tectonic': version,
               'tectonic_binary_sha256': sha(a.tectonic), 'exit_code': run.returncode,
               'source_date_epoch': env['SOURCE_DATE_EPOCH']}
    if run.returncode == 0:
        subprocess.run(['pdftotext', '-layout', str(out / 'main.pdf'), str(out / 'main.txt')], check=True)
        info = subprocess.check_output(['pdfinfo', str(out / 'main.pdf')], text=True)
        (out / 'pdfinfo.txt').write_text(info)
        receipt['pdf_sha256'] = sha(out / 'main.pdf')
    (out / 'build-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(run.stdout + run.stderr)
    raise SystemExit(run.returncode)

if __name__ == '__main__':
    main()
