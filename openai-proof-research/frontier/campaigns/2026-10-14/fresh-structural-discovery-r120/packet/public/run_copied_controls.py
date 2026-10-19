#!/usr/bin/env python3
"""MIT; Myeongjin Kang. Adapted from structural r119/r81 copied controls.
Writes only root/controls. Original verifier is used on disposable copies.
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
    out = {}
    for p in sorted(root.rglob('*')):
        s = p.lstat()
        out[p.relative_to(root).as_posix()] = {'mode': s.st_mode, 'links': s.st_nlink,
                                              'hash': digest(p.read_bytes()) if p.is_file() else None}
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True, type=Path)
    ap.add_argument('--tree', required=True, type=Path)
    ap.add_argument('--finalhash', required=True)
    ap.add_argument('--reporthash', required=True)
    args = ap.parse_args()
    root = args.root.resolve()
    controls = root / 'controls'
    controls.mkdir(exist_ok=True)
    verifier = root / 'packet/public/verify.py'
    anchors = ['FINAL.json', 'MANIFEST.json', 'REPORT.md']
    before = inventory(root / 'packet')
    abefore = {n: digest((root/n).read_bytes()) for n in anchors}
    rows = []

    def run(name, mutate=None, omit=None, wrong=None, expected='reject'):
        with tempfile.TemporaryDirectory(prefix=name+'-', dir=controls) as temp:
            copy = Path(temp) / 'copy'
            copy.mkdir()
            shutil.copytree(root/'packet', copy/'packet', symlinks=True)
            for n in anchors:
                shutil.copy2(root/n, copy/n)
            tree = Path(temp)/'tree.json'
            shutil.copy2(args.tree, tree)
            if mutate:
                mutate(copy, tree)
            cmd = [sys.executable, '-B', str(verifier), '--root', str(copy)]
            vals = {'tree':str(tree), 'finalhash':args.finalhash, 'reporthash':args.reporthash}
            if wrong:
                vals[wrong] = '0'*64
            for k, v in vals.items():
                if omit != k:
                    cmd += ['--'+k, v]
            p = subprocess.run(cmd, capture_output=True, text=True)
            ok = p.returncode == 0 if expected == 'accept' else p.returncode != 0
            rows.append({'case': name, 'expected': expected, 'returncode': p.returncode,
                         'passed': ok, 'stdout':p.stdout, 'stderr':p.stderr,
                         'original_verifier': True, 'copied_packet': True})

    payload = 'packet/public/artin-search.md'
    def change(c,t):
        f=c/payload
        f.write_bytes(f.read_bytes()+b'\nCONTROL MUTATION\n')
    def filelink(c,t):
        f=c/payload
        f.unlink()
        f.symlink_to(c/'packet/public/report.md')
    def hardlink(c,t):
        f=c/payload
        f.unlink()
        os.link(c/'packet/public/report.md', f)
    def dirlink(c,t):
        d=c/'packet/private/primary'
        shutil.rmtree(d)
        d.symlink_to(root/'packet/private/primary', target_is_directory=True)
    def reseal(c,t):
        change(c,t)
        m=json.loads((c/'MANIFEST.json').read_text())
        for e in m['files']:
            if e['path']=='public/artin-search.md':
                b=(c/payload).read_bytes()
                e.update(bytes=len(b),sha256=digest(b))
        (c/'MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
        f=json.loads((c/'FINAL.json').read_text())
        f['manifest_sha256']=digest((c/'MANIFEST.json').read_bytes())
        (c/'FINAL.json').write_text(json.dumps(f,indent=2)+'\n')

    run('clean-copy', expected='accept')
    run('missing-finalhash', omit='finalhash')
    run('wrong-finalhash', wrong='finalhash')
    run('missing-reporthash', omit='reporthash')
    run('wrong-reporthash', wrong='reporthash')
    run('missing-tree', omit='tree')
    run('changed-tree', lambda c,t:t.write_text('{}'))
    run('changed-payload',change)
    run('missing-payload',lambda c,t:(c/payload).unlink())
    run('extra-file',lambda c,t:(c/'packet/public/extra.txt').write_text('extra'))
    run('extra-directory',lambda c,t:(c/'packet/public/extra').mkdir())
    run('file-symlink',filelink)
    run('file-hardlink',hardlink)
    run('directory-symlink',dirlink)
    run('changed-report',lambda c,t:(c/'REPORT.md').write_text('changed'))
    run('changed-manifest',lambda c,t:(c/'MANIFEST.json').write_text('{}'))
    run('coherent-reseal-old-anchor',reseal)
    run('changed-verifier',lambda c,t:(c/'packet/public/verify.py').write_text('print("ok")\n'))
    unchanged = before == inventory(root/'packet') and abefore == {n:digest((root/n).read_bytes()) for n in anchors}
    result={'scope':'INTEGRITY_ONLY','finalhash':args.finalhash,'reporthash':args.reporthash,
            'cases':rows,'all_expected':all(e['passed'] for e in rows),
            'original_unchanged':unchanged,'mathematical_gate':False}
    (controls/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='cases'},sort_keys=True))
    if not result['all_expected'] or not unchanged:
        raise SystemExit(1)


if __name__=='__main__':
    main()
