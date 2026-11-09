#!/usr/bin/env python3
"""Mutate only copies under this r104 root/work/controls. Never modify originals.
Anchor arguments must be supplied externally. Invokes the original verifier read-only.
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

def digest(b):
    return hashlib.sha256(b).hexdigest()

def snapshot(root):
    out = {}
    for base in (root/'packet', root/'REPORT.md'):
        todo = [base]
        while todo:
            p = todo.pop()
            s = p.lstat()
            record = {'mode': stat.S_IMODE(s.st_mode), 'kind': stat.S_IFMT(s.st_mode)}
            if p.is_symlink():
                record['link'] = os.readlink(p)
            elif p.is_dir():
                todo.extend(p.iterdir())
            elif p.is_file():
                record['sha256'] = digest(p.read_bytes())
                record['size'] = s.st_size
            out[str(p.relative_to(root))] = record
    return out

def main():
    a = argparse.ArgumentParser(description=__doc__)
    for name in ('final', 'manifest', 'report'):
        a.add_argument('--' + name + '-sha256', required=True)
    args = a.parse_args()
    root = Path(__file__).resolve().parents[2]
    if root.name != 'fresh-arithmetic-discovery-r104':
        raise ValueError('controls run only from the assigned original r104 root')
    target = root/'work/controls'
    target.mkdir(parents=True, exist_ok=True)
    before = snapshot(root)
    names = ['baseline','payload','missing','extra_file','extra_directory','symlink','wrong_anchor','manifest','report','forged_reseal']
    results = []
    for name in names:
        dest = target/name
        dest.mkdir()  # Never overwrite an earlier control run.
        shutil.copytree(root/'packet', dest/'packet', symlinks=True)
        shutil.copy2(root/'REPORT.md', dest/'REPORT.md')
        payload = dest/'packet/public/growth_check.json'
        anchor = args.final_sha256
        if name == 'payload':
            payload.write_bytes(payload.read_bytes()+b'\n')
        elif name == 'missing':
            payload.unlink()
        elif name == 'extra_file':
            (dest/'packet/extra').write_text('unexpected\n')
        elif name == 'extra_directory':
            (dest/'packet/extra').mkdir()
        elif name == 'symlink':
            payload.unlink(); payload.symlink_to('DERIVATION.md')
        elif name == 'wrong_anchor':
            anchor = ('0' if anchor[0] != '0' else '1') + anchor[1:]
        elif name == 'manifest':
            f = dest/'packet/MANIFEST.json';f.write_bytes(f.read_bytes()+b'\n')
        elif name == 'report':
            f = dest/'REPORT.md';f.write_bytes(f.read_bytes()+b'\n')
        elif name == 'forged_reseal':
            payload.write_bytes(payload.read_bytes()+b'\n')
            m = dest/'packet/MANIFEST.json';j = json.loads(m.read_text())
            j['payloads']['public/growth_check.json']['sha256'] = digest(payload.read_bytes())
            j['payloads']['public/growth_check.json']['size'] = payload.stat().st_size
            m.write_text(json.dumps(j,indent=2)+'\n')
            f = dest/'packet/FINAL.json';j = json.loads(f.read_text());j['manifest_sha256'] = digest(m.read_bytes());f.write_text(json.dumps(j,indent=2)+'\n')
        fixture_before = snapshot(dest)
        cmd = [sys.executable,'-B',str(root/'packet/public/verify.py'),'--root',str(dest),'--final-sha256',anchor,'--manifest-sha256',args.manifest_sha256,'--report-sha256',args.report_sha256]
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
        readonly = snapshot(dest) == fixture_before
        expected = (p.returncode == 0) if name == 'baseline' else (p.returncode != 0)
        results.append({'case':name,'expected_behavior':expected,'fixture_unchanged_by_verifier':readonly,'returncode':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
    original_unchanged = snapshot(root) == before
    report = {'original_sealed_packet_and_report_unchanged':original_unchanged,'cases':results,'all_controls_pass':original_unchanged and all(x['expected_behavior'] and x['fixture_unchanged_by_verifier'] for x in results),'meaning':'Artifact-integrity controls only; no mathematical gate'}
    (root/'work/controls-results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    if not report['all_controls_pass']:
        sys.exit(1)

if __name__ == '__main__':
    main()
