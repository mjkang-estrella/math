#!/usr/bin/env python3
"""Disposable-copy integrity controls, never mathematical tests. MIT."""
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


def snapshot(root, ignored=()):
    out = {}
    for p in [root] + sorted(root.rglob('*')):
        rel = p.relative_to(root).as_posix()
        if any(rel == x or rel.startswith(x + '/') for x in ignored):
            continue
        s = p.lstat()
        value = [s.st_mode, s.st_nlink]
        if stat.S_ISREG(s.st_mode):
            value += [s.st_size, sha(p.read_bytes())]
        elif stat.S_ISLNK(s.st_mode):
            value += [os.readlink(p)]
        out[rel] = value
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True)
    ap.add_argument('--finalhash', required=True)
    ap.add_argument('--reporthash', required=True)
    ap.add_argument('--canonical-tree', required=True)
    a = ap.parse_args()
    root = Path(a.root).resolve()
    tree = Path(a.canonical_tree).resolve()
    work = root / '.control-work'
    if work.exists():
        raise RuntimeError('Refuse existing control-work')
    # Authentication BEFORE copying; never derive trust anchors from selected root.
    base_args = ['--finalhash', a.finalhash, '--reporthash', a.reporthash, '--canonical-tree', str(tree)]
    initial = subprocess.run([sys.executable, '-B', str(root/'packet/public/verify.py'), '--root', str(root)] + base_args, capture_output=True, text=True)
    if initial.returncode:
        raise RuntimeError(initial.stderr)
    before = snapshot(root, ('integrity-results.json', '.control-work'))
    results = []
    cases = [
        ('baseline', ''), ('missing-final-anchor', '--finalhash'), ('wrong-final-anchor', 'FINAL_HASH'),
        ('wrong-report-anchor', 'REPORT_HASH'), ('payload-change', 'PAYLOAD_INVENTORY_HASH_MODE'),
        ('payload-missing', 'PAYLOAD_INVENTORY_HASH_MODE'), ('payload-extra', 'PAYLOAD_INVENTORY_HASH_MODE'),
        ('directory-extra', 'DIRECTORY_INVENTORY_MODE'), ('directory-mode', 'DIRECTORY_INVENTORY_MODE'),
        ('payload-mode', 'PAYLOAD_INVENTORY_HASH_MODE'), ('symlink', 'REGULAR_SINGLE_LINK'),
        ('hardlink', 'REGULAR_SINGLE_LINK'), ('manifest-change', 'MANIFEST_HASH'),
        ('report-change', 'REPORT_HASH'), ('verifier-change', 'VERIFIER_HASH'),
        ('final-change', 'FINAL_HASH'), ('external-tree-change', 'EXTERNAL_TREE_HASH'),
        ('coherent-reseal-old-anchor', 'FINAL_HASH'),
    ]
    work.mkdir()
    try:
        for name, reason in cases:
            c = work / 'copy'
            c.mkdir()
            shutil.copytree(root/'packet', c/'packet')
            for f in ['FINAL.json', 'REPORT.md']:
                shutil.copy2(root/f, c/f)
            args = list(base_args)
            payload = c/'packet/public/automorphism-feasibility.md'
            if name == 'missing-final-anchor':
                args = args[2:]
            elif name == 'wrong-final-anchor': args[1] = '0'*64
            elif name == 'wrong-report-anchor': args[3] = '0'*64
            elif name == 'payload-change': payload.write_bytes(payload.read_bytes()+b'\nMUTATION\n')
            elif name == 'payload-missing': payload.unlink()
            elif name == 'payload-extra': (c/'packet/unexpected').write_text('extra')
            elif name == 'directory-extra': (c/'packet/unexpected-dir').mkdir()
            elif name == 'directory-mode': (c/'packet/public').chmod(0o700)
            elif name == 'payload-mode': payload.chmod(0o600)
            elif name == 'symlink':
                payload.unlink(); payload.symlink_to('report.md')
            elif name == 'hardlink': os.link(payload, c/'packet/extra-hardlink')
            elif name == 'manifest-change': (c/'packet/MANIFEST.json').write_text('{}\n')
            elif name == 'report-change': (c/'REPORT.md').write_text('MUTATION\n')
            elif name == 'verifier-change':
                v=c/'packet/public/verify.py'; v.write_bytes(v.read_bytes()+b'\n# MUTATION\n')
            elif name == 'final-change': (c/'FINAL.json').write_text('{}\n')
            elif name == 'external-tree-change':
                t=c/'wrong-tree.json'; t.write_bytes(tree.read_bytes()+b'\n'); args[-1]=str(t)
            elif name == 'coherent-reseal-old-anchor':
                payload.write_bytes(payload.read_bytes()+b'\nMUTATION\n')
                m=c/'packet/MANIFEST.json'; j=json.loads(m.read_text())
                row=j['files']['public/automorphism-feasibility.md']; row.update(sha256=sha(payload.read_bytes()), bytes=payload.stat().st_size)
                m.write_text(json.dumps(j,indent=2)+'\n')
                f=c/'FINAL.json'; j=json.loads(f.read_text()); j['manifest_sha256']=sha(m.read_bytes()); f.write_text(json.dumps(j,indent=2)+'\n')
            copied_before = snapshot(c)
            run=subprocess.run([sys.executable,'-B',str(c/'packet/public/verify.py'),'--root',str(c)]+args,capture_output=True,text=True)
            unchanged=snapshot(c)==copied_before
            expected=(run.returncode==0) if name=='baseline' else (run.returncode!=0 and reason in run.stderr)
            results.append({'case':name,'returncode':run.returncode,'expected_diagnostic':reason,
                            'expected':expected,'copied_inputs_unchanged':unchanged,
                            'stdout':run.stdout.strip(),'stderr':run.stderr.strip()})
            if not expected or not unchanged:
                raise RuntimeError('CONTROL FAILED '+name+' '+run.stderr)
            shutil.rmtree(c)
    finally:
        shutil.rmtree(work)
    unchanged = snapshot(root, ('integrity-results.json', '.control-work')) == before
    if not unchanged:
        raise RuntimeError('ORIGINAL CHANGED')
    result={'status':'INTEGRITY_ONLY','final_sha256':a.finalhash,'report_sha256':a.reporthash,
            'initial_verifier':json.loads(initial.stdout),'cases':results,
            'original_unchanged':unchanged,'cases_expected':len(results),
            'audit_denial_probes':False,'mathematical_tests':False,
            'limits':'No malicious-code sandbox/race claim. Ordinary mutations test enclosing hash/path controls, not independently isolated semantic parsers. Whole-root preservation excludes the new receipt and transient work root.'}
    (root/'integrity-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'cases_expected':len(results),'original_unchanged':unchanged,'receipt_sha256':sha((root/'integrity-results.json').read_bytes())}))


if __name__=='__main__':
    main()
