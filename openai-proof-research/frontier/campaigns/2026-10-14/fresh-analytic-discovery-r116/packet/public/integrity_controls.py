#!/usr/bin/env python3
"""Disposable-copy integrity controls, never mathematical gates.
Adapted to this packet from the project's copied-control convention.
All writes stay under the explicitly supplied owned directory.
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

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def snapshot(p):
    return {str(f.relative_to(p)): (f.stat().st_mode & 0o7777, sha(f))
            for f in p.rglob('*') if f.is_file()}

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--owned', type=Path, required=True)
    ap.add_argument('--finalhash', required=True)
    ap.add_argument('--finalanchor', required=True)
    a = ap.parse_args()
    owned = a.owned.resolve()
    packet = owned / 'packet'
    final = owned / 'FINAL.json'
    verifier = packet / 'public/verify.py'
    old = snapshot(packet)
    old_final = final.read_bytes()
    assert sha(packet / 'manifest.json') == a.finalhash
    assert sha(final) == a.finalanchor
    cases = ['baseline', 'wrong-manifest-anchor', 'missing-manifest-anchor',
             'wrong-FINAL-anchor', 'missing-FINAL-anchor', 'changed-report',
             'changed-proof', 'changed-frozen-target', 'changed-source',
             'changed-primary', 'missing-file', 'extra-file', 'extra-directory',
             'symlink', 'hardlink', 'changed-mode', 'changed-root-mode',
             'changed-manifest', 'resealed-report', 'changed-FINAL-metadata',
             'resealed-manifest-and-FINAL', 'changed-verifier-payload']
    results = []
    work = owned / 'work'
    work.mkdir(exist_ok=True)
    for case in cases:
        with tempfile.TemporaryDirectory(prefix='integrity-copy-', dir=work) as td:
            base = Path(td)
            cp = base / 'packet'
            cf = base / 'FINAL.json'
            shutil.copytree(packet, cp)
            shutil.copy2(final, cf)
            report = cp / 'public/research-report.md'
            manifest = cp / 'manifest.json'
            if case in ('changed-report', 'resealed-report', 'resealed-manifest-and-FINAL'):
                report.write_bytes(report.read_bytes()+b'\nchanged\n')
            if case in ('resealed-report', 'resealed-manifest-and-FINAL'):
                m = json.loads(manifest.read_text())
                m['files']['public/research-report.md']['bytes'] = report.stat().st_size
                m['files']['public/research-report.md']['sha256'] = sha(report)
                manifest.write_text(json.dumps(m, sort_keys=True, indent=2)+'\n')
            if case == 'resealed-manifest-and-FINAL':
                f = json.loads(cf.read_text())
                f['manifest_sha256'] = sha(manifest)
                f['report_sha256'] = sha(report)
                cf.write_text(json.dumps(f, sort_keys=True, indent=2)+'\n')
            mutations = {'changed-proof':'public/proof.md',
                         'changed-frozen-target':'public/frozen-target.md',
                         'changed-source':'private/upstream/152/04-switching.tex',
                         'changed-primary':'private/primary/katok-thouvenot1997.pdf',
                         'changed-verifier-payload':'public/verify.py'}
            if case in mutations:
                f=cp/mutations[case]; f.write_bytes(f.read_bytes()+b'\nchanged\n')
            if case == 'missing-file': report.unlink()
            if case == 'extra-file': (cp/'unexpected').write_text('extra')
            if case == 'extra-directory': (cp/'empty-extra').mkdir()
            if case == 'symlink':
                report.unlink(); report.symlink_to('proof.md')
            if case == 'hardlink':
                report.unlink(); os.link(cp/'public/proof.md', report)
            if case == 'changed-mode': report.chmod(0o600)
            if case == 'changed-root-mode': cp.chmod(0o700)
            if case == 'changed-manifest': manifest.write_bytes(manifest.read_bytes()+b' ')
            if case == 'changed-FINAL-metadata':
                f=json.loads(cf.read_text()); f['candidate']='forged'
                cf.write_text(json.dumps(f,sort_keys=True,indent=2)+'\n')
            cmd=[sys.executable,'-B',str(verifier),'--packet',str(cp),
                 '--finalfile',str(cf)]
            if case != 'missing-manifest-anchor':
                cmd += ['--finalhash', '0'*64 if case=='wrong-manifest-anchor' else a.finalhash]
            if case != 'missing-FINAL-anchor':
                cmd += ['--finalanchor','0'*64 if case=='wrong-FINAL-anchor' else a.finalanchor]
            before=snapshot(cp); fb=cf.read_bytes()
            result=subprocess.run(cmd,text=True,capture_output=True)
            unchanged=(snapshot(cp)==before and cf.read_bytes()==fb)
            expected=(case=='baseline')
            ok=((result.returncode==0)==expected and unchanged)
            results.append({'case':case,'expected_accept':expected,'returncode':result.returncode,
                            'output':(result.stdout+result.stderr).strip(),
                            'verifier_read_only':unchanged,'control_passed':ok,
                            'copied_FINAL_sha256':sha(cf)})
    original_ok=(snapshot(packet)==old and final.read_bytes()==old_final)
    record={'schema':'r116-copied-integrity-controls-v1','manifest_sha256':a.finalhash,
            'FINAL_sha256':a.finalanchor,'report_sha256':sha(packet/'public/research-report.md'),
            'original_packet_and_FINAL_unchanged':original_ok,'results':results,
            'mathematical_assessment':'none','contribution_assessment':'none'}
    (owned/'integrity-controls.json').write_text(json.dumps(record,sort_keys=True,indent=2)+'\n')
    print(json.dumps({'controls':len(results),'passed':sum(x['control_passed'] for x in results),
                      'originals_unchanged':original_ok,'FINAL_sha256':a.finalanchor},sort_keys=True))
    return 0 if original_ok and all(x['control_passed'] for x in results) else 1

if __name__=='__main__':
    raise SystemExit(main())
