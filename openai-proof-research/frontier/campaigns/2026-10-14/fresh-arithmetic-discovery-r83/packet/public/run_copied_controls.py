#!/usr/bin/env python3
"""MIT; Myeongjin Kang. Adapted from arithmetic r82. Integrity controls only; writes only within root/controls.

Run after sealing, with the detached FINAL hash. Uses temporary copies and the
unchanged original verifier. No mathematical tests or acceptance decisions.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def digest(b):
    return hashlib.sha256(b).hexdigest()


def inventory(root):
    result = {}
    for p in sorted(root.rglob('*')):
        rel = p.relative_to(root).as_posix()
        if rel == 'controls' or rel.startswith('controls/'):
            continue
        if p.is_symlink():
            result[rel] = {'symlink':os.readlink(p)}
        elif p.is_file():
            result[rel] = {'sha256':digest(p.read_bytes())}
        elif p.is_dir():
            result[rel] = {'directory':True}
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True, type=Path)
    ap.add_argument('--finalhash', required=True)
    args = ap.parse_args()
    root = args.root.resolve()
    verifier = root / 'packet/public/verify.py'
    controls = root / 'controls'
    controls.mkdir(exist_ok=True)
    before = inventory(root)
    anchors_before = {n: digest((root/n).read_bytes()) for n in ['MANIFEST.json', 'FINAL.json', 'REPORT.md']}
    rows = []

    def run(label, mutate=None, anchor=True, expected=1):
        with tempfile.TemporaryDirectory(prefix=label+'-', dir=controls) as temp:
            copy = Path(temp)/'copy'
            copy.mkdir()
            shutil.copytree(root/'packet', copy/'packet', symlinks=True)
            for name in ['MANIFEST.json', 'FINAL.json', 'REPORT.md']:
                shutil.copy2(root/name, copy/name)
            if mutate:
                mutate(copy)
            cmd = [sys.executable, '-B', str(verifier), '--root', str(copy)]
            if anchor is not False:
                cmd += ['--finalhash', args.finalhash if anchor is True else anchor]
            result = subprocess.run(cmd, capture_output=True, text=True)
            passed = result.returncode == 0 if expected == 0 else result.returncode != 0
            rows.append({'case':label,'expected':'accept' if expected == 0 else 'reject',
                         'returncode':result.returncode,'passed':passed,
                         'stdout':result.stdout,'stderr':result.stderr,
                         'copied_packet':True,'original_verifier':True})

    payload = 'packet/public/research.md'
    def change(p):
        f=p/payload
        f.write_bytes(f.read_bytes()+b'\nCONTROL MUTATION\n')
    def file_link(p):
        f=p/payload
        f.unlink()
        f.symlink_to(root/payload)
    def dir_link(p):
        d=p/'packet/private/primary'
        shutil.rmtree(d)
        d.symlink_to(root/'packet/private/primary', target_is_directory=True)
    def reseal(p):
        change(p)
        m=json.loads((p/'MANIFEST.json').read_text())
        for e in m['files']:
            if e['path']=='public/research.md':
                b=(p/payload).read_bytes()
                e.update(bytes=len(b),sha256=digest(b))
        (p/'MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
        f=json.loads((p/'FINAL.json').read_text())
        f['manifest_sha256']=digest((p/'MANIFEST.json').read_bytes())
        (p/'FINAL.json').write_text(json.dumps(f,indent=2)+'\n')

    run('clean-copy',expected=0)
    run('missing-anchor',anchor=False)
    run('wrong-anchor',anchor='0'*64)
    run('changed-payload',change)
    run('missing-payload',lambda p:(p/payload).unlink())
    run('extra-file',lambda p:(p/'packet/public/extra.txt').write_text('extra'))
    run('extra-empty-directory',lambda p:(p/'packet/public/extra').mkdir())
    run('file-symlink',file_link)
    run('directory-symlink',dir_link)
    run('changed-report',lambda p:(p/'REPORT.md').write_text('changed'))
    run('changed-manifest',lambda p:(p/'MANIFEST.json').write_text('{}'))
    run('coherent-reseal-old-anchor',reseal)
    run('changed-verifier',lambda p:(p/'packet/public/verify.py').write_text('print("ok")\n'))
    original_unchanged = (before == inventory(root) and anchors_before ==
        {n:digest((root/n).read_bytes()) for n in anchors_before})
    result = {'scope':'INTEGRITY_ONLY','finalhash':args.finalhash,'cases':rows,
              'original_unchanged':original_unchanged,
              'all_expected':all(r['passed'] for r in rows),
              'mathematical_verification':False}
    (controls/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='cases'},sort_keys=True))
    if not result['all_expected'] or not original_unchanged:
        raise SystemExit(1)


if __name__=='__main__':
    main()
