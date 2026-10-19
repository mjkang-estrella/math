#!/usr/bin/env python3
"""Mutate disposable copies only; check the detached FINAL anchor and unchanged original.
Not a mathematical gate. The verifier invoked is the separately anchored original code.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys

sha = lambda b: hashlib.sha256(b).hexdigest()

def snapshot(root):
    entries = {}
    for f in [root] + sorted(root.rglob('*')):
        s = f.lstat()
        key = '.' if f == root else f.relative_to(root).as_posix()
        entries[key] = [stat.S_IMODE(s.st_mode), s.st_nlink,
                        sha(f.read_bytes()) if f.is_file() else None]
    return entries

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--packet', required=True, type=Path)
    ap.add_argument('--anchor', required=True, type=Path)
    ap.add_argument('--work', required=True, type=Path)
    args = ap.parse_args()
    root, anchor, work = (p.absolute() for p in (args.packet, args.anchor, args.work))
    if root in work.parents or work == root or work.exists():
        raise ValueError('control directory must be absent and outside packet')
    # All copy writes remain inside the assigned round directory.
    if root.parent not in work.parents:
        raise ValueError('control directory must be inside the owned round directory')
    raw_anchor = anchor.read_bytes()
    final = json.loads(raw_anchor)
    before = snapshot(root)
    verifier = root/'public/verify.py'
    assert sha(verifier.read_bytes()) == final['verifier_sha256']
    work.mkdir(parents=True)
    results = []
    cases = ['baseline','wrong-anchor','missing-anchor','changed-report','changed-source',
             'changed-primary','missing-file','extra-file','extra-directory','symlink',
             'hardlink','changed-mode','changed-manifest','resealed-report','changed-FINAL']
    for case in cases:
        home = work/case
        home.mkdir()
        target = home/'packet'
        shutil.copytree(root,target)
        copied_anchor = home/'FINAL.json'
        copied_anchor.write_bytes(raw_anchor)
        supplied = json.loads(copied_anchor.read_bytes())['manifest_sha256']
        report = target/'public/research-report.md'
        if case == 'wrong-anchor': supplied = '0'*64
        elif case == 'changed-report': report.write_bytes(report.read_bytes()+b'\nchanged\n')
        elif case == 'changed-source':
            f = next((target/'private/upstream').rglob('*.tex')); f.write_bytes(f.read_bytes()+b'\nchanged\n')
        elif case == 'changed-primary':
            f = next((target/'private/primary').glob('*.pdf')); f.write_bytes(f.read_bytes()+b'changed')
        elif case == 'missing-file': report.unlink()
        elif case == 'extra-file': (target/'extra').write_text('x')
        elif case == 'extra-directory': (target/'extra-empty').mkdir()
        elif case == 'symlink': report.unlink(); report.symlink_to(root/'public/research-report.md')
        elif case == 'hardlink':
            report.unlink(); donor=home/'donor'; donor.write_bytes((root/'public/research-report.md').read_bytes()); os.link(donor,report)
        elif case == 'changed-mode': report.chmod(stat.S_IMODE(report.stat().st_mode)^stat.S_IXUSR)
        elif case == 'changed-manifest':
            f=target/'manifest.json'; f.write_bytes(f.read_bytes()+b' ')
        elif case == 'resealed-report':
            report.write_bytes(report.read_bytes()+b'\nchanged\n')
            f=target/'manifest.json'; m=json.loads(f.read_bytes()); e=m['files']['public/research-report.md']; e['bytes']=report.stat().st_size; e['sha256']=sha(report.read_bytes()); f.write_text(json.dumps(m,sort_keys=True,indent=2)+'\n')
        elif case == 'changed-FINAL':
            changed=json.loads(raw_anchor);changed['manifest_sha256']='0'*64
            copied_anchor.write_text(json.dumps(changed)+'\n')
            supplied=json.loads(copied_anchor.read_bytes())['manifest_sha256']
        cmd=[sys.executable,'-B',str(verifier),'--packet',str(target)]
        if case != 'missing-anchor': cmd += ['--finalhash',supplied]
        r=subprocess.run(cmd,capture_output=True,text=True,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
        expected_accept = case == 'baseline'
        assert (r.returncode == 0) == expected_accept, (case,r.stdout,r.stderr)
        results.append(dict(case=case,expected_accept=expected_accept,returncode=r.returncode,
                            output=(r.stdout+r.stderr).strip(),copied_final_sha256=sha(copied_anchor.read_bytes())))
        # Retain small results, not fifteen duplicate PDF collections.
        shutil.rmtree(target)
        donor=home/'donor'
        if donor.exists(): donor.unlink()
    assert before == snapshot(root), 'original packet changed'
    assert anchor.read_bytes() == raw_anchor, 'original FINAL changed'
    output=dict(schema='r115-copied-controls-v1',manifest_sha256=final['manifest_sha256'],
                report_sha256=final['report_sha256'],final_file_sha256=sha(raw_anchor),
                original_packet_unchanged=True,original_FINAL_unchanged=True,
                mathematical_gate=False,contribution_gate=False,results=results)
    print(json.dumps(output,sort_keys=True,indent=2))

if __name__ == '__main__':
    main()
