#!/usr/bin/env python3
"""Exercise only copies; the sealed original is never mutated."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).absolute().parent
PACKET = HERE / 'packet'
FINALHASH = '415cc5ab3688cd81263aa590993dd37c9ddb4d939b39c9b2fea0f231fca72665'

def inventory():
    return {str(p.relative_to(PACKET)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in PACKET.rglob('*') if p.is_file()}

before = inventory()
assert before['manifest.json'] == FINALHASH
out = []
for case in ['baseline', 'omitted-finalhash', 'wrong-finalhash', 'corrupt-payload',
             'missing-payload', 'extra-payload', 'extra-directory', 'symlink-payload',
             'hardlink-payload', 'changed-manifest', 'symlink-root', 'resealed-wrong-pin']:
    with tempfile.TemporaryDirectory(prefix='control-', dir=HERE) as tmp:
        root = Path(tmp) / 'packet'
        shutil.copytree(PACKET, root)
        target = root / 'public/research.md'
        packet_arg = root
        finalhash = FINALHASH
        if case == 'corrupt-payload':
            target.write_bytes(target.read_bytes() + b'changed\n')
        elif case == 'missing-payload':
            target.unlink()
        elif case == 'extra-payload':
            (root / 'unexpected.txt').write_text('extra')
        elif case == 'extra-directory':
            (root / 'unexpected').mkdir()
        elif case in ('symlink-payload', 'hardlink-payload'):
            other = Path(tmp) / 'original-copy.md'
            shutil.copyfile(target, other)
            target.unlink()
            if case == 'symlink-payload':
                target.symlink_to(other)
            else:
                os.link(other, target)
        elif case == 'changed-manifest':
            m = root / 'manifest.json'
            m.write_bytes(m.read_bytes() + b' ')
        elif case == 'symlink-root':
            packet_arg = Path(tmp) / 'linked-packet'
            packet_arg.symlink_to(root, target_is_directory=True)
        elif case == 'resealed-wrong-pin':
            m = root / 'manifest.json'
            body = json.loads(m.read_text()); body['pin'] = '0' * 40
            m.write_text(json.dumps(body, indent=2) + '\n')
            finalhash = hashlib.sha256(m.read_bytes()).hexdigest()
        elif case == 'wrong-finalhash':
            finalhash = '0' * 64
        command = [sys.executable, '-B', str(root / 'public/verify.py'), '--packet', str(packet_arg)]
        if case != 'omitted-finalhash':
            command.extend(['--finalhash', finalhash])
        run = subprocess.run(command, capture_output=True, text=True)
        combined = run.stdout + run.stderr
        expected = {'baseline': '"integrity": "verified"',
                    'omitted-finalhash': 'required: --finalhash',
                    'wrong-finalhash': 'detached manifest hash mismatch',
                    'corrupt-payload': 'payload hash mismatch',
                    'missing-payload': 'file inventory mismatch',
                    'extra-payload': 'file inventory mismatch',
                    'extra-directory': 'directory inventory mismatch',
                    'symlink-payload': 'symlink payload',
                    'hardlink-payload': 'hardlinked payload',
                    'changed-manifest': 'detached manifest hash mismatch',
                    'symlink-root': 'symlink ancestor',
                    'resealed-wrong-pin': 'wrong upstream pin'}[case]
        passed = (run.returncode == 0) == (case == 'baseline') and expected in combined
        out.append({'case':case, 'expected_behavior_observed':passed,
                    'returncode':run.returncode,'output':combined.strip()})
        print(case, passed)
after = inventory()
report = {'packet_manifest_sha256':FINALHASH, 'copied_controls':out,
          'sealed_original_unchanged':before == after,
          'all_expected_behaviors_observed':all(x['expected_behavior_observed'] for x in out),
          'mathematical_gate':False}
(HERE / 'integrity-controls.json').write_text(json.dumps(report, indent=2) + '\n')
assert before == after and report['all_expected_behaviors_observed']
