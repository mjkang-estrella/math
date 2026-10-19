#!/usr/bin/env python3
"""MIT. Disposable-copy artifact controls. Writes only below --root/work.
Does not execute author code, alter originals, or test mathematics.
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


def sha(b):
    return hashlib.sha256(b).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', type=Path, required=True)
    ap.add_argument('--project-root', type=Path, required=True)
    ap.add_argument('--expected-final', required=True)
    ap.add_argument('--expected-report', required=True)
    a = ap.parse_args()
    root = a.root.resolve()
    work = root / 'work'
    work.mkdir(exist_ok=True)
    trusted_verifier = root / 'packet/public/verify.py'
    results = []

    def check(target, seal=a.expected_final, report=a.expected_report):
        return subprocess.run([sys.executable, '-B', str(trusted_verifier), '--root', str(target),
                               '--project-root', str(a.project_root.resolve()),
                               '--expected-final', seal, '--expected-report', report],
                              capture_output=True, text=True, env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})

    initial = check(root)
    if initial.returncode:
        raise RuntimeError('Original baseline failed: ' + initial.stderr)
    results.append({'name': 'original_before', 'expected': 'PASS', 'returncode': 0, 'stdout': initial.stdout})
    cases = [('pristine_copy', True), ('payload_byte', False), ('missing_payload', False),
             ('extra_payload', False), ('renamed_payload', False), ('extra_empty_directory', False),
             ('symlink_payload', False), ('manifest_byte', False), ('coordinated_reseal_old_anchor', False),
             ('outside_report', False), ('outside_final', False), ('wrong_external_final', False),
             ('wrong_external_report', False), ('permission_mode_not_bound', True), ('hardlink_count_not_bound', True)]
    for name, succeeds in cases:
        with tempfile.TemporaryDirectory(prefix='copy-', dir=work) as tmp:
            target = Path(tmp)
            shutil.copytree(root / 'packet', target / 'packet', copy_function=shutil.copy2)
            for n in ('REPORT.md', 'REPORT.sha256', 'FINAL'):
                shutil.copy2(root / n, target / n)
            payload = target / 'packet/public/review.md'
            seal, report = a.expected_final, a.expected_report
            if name == 'payload_byte':
                payload.write_bytes(payload.read_bytes() + b'\nCONTROL\n')
            elif name == 'missing_payload':
                payload.unlink()
            elif name == 'extra_payload':
                (target / 'packet/public/extra').write_text('CONTROL\n')
            elif name == 'renamed_payload':
                payload.rename(payload.with_name('renamed.md'))
            elif name == 'extra_empty_directory':
                (target / 'packet/public/empty').mkdir()
            elif name == 'symlink_payload':
                backup = target / 'local-copy.md'
                payload.rename(backup)
                payload.symlink_to(backup)
            elif name == 'manifest_byte':
                m = target / 'packet/MANIFEST.json'
                m.write_bytes(m.read_bytes() + b' ')
            elif name == 'coordinated_reseal_old_anchor':
                payload.write_bytes(payload.read_bytes() + b'\nCONTROL\n')
                m = target / 'packet/MANIFEST.json'
                body = json.loads(m.read_bytes())
                data = payload.read_bytes()
                body['files']['public/review.md'] = {'bytes': len(data), 'sha256': sha(data)}
                m.write_text(json.dumps(body, sort_keys=True, indent=2) + '\n')
                (target / 'FINAL').write_text(sha(m.read_bytes()) + '\n')
            elif name == 'outside_report':
                p = target / 'REPORT.md'
                p.write_bytes(p.read_bytes() + b'CONTROL')
            elif name == 'outside_final':
                (target / 'FINAL').write_text('0' * 64 + '\n')
            elif name == 'wrong_external_final':
                seal = '0' * 64
            elif name == 'wrong_external_report':
                report = '0' * 64
            elif name == 'permission_mode_not_bound':
                payload.chmod(0o600)
            elif name == 'hardlink_count_not_bound':
                os.link(payload, target / 'outside-packet-hardlink.md')
            before = {str(p.relative_to(target)): sha(p.read_bytes()) for p in target.rglob('*') if p.is_file() and not p.is_symlink()}
            outcome = check(target, seal, report)
            after = {str(p.relative_to(target)): sha(p.read_bytes()) for p in target.rglob('*') if p.is_file() and not p.is_symlink()}
            if before != after:
                raise RuntimeError('Verifier changed copy: ' + name)
            if (outcome.returncode == 0) != succeeds:
                raise RuntimeError('Unexpected control result: ' + name + '\n' + outcome.stdout + outcome.stderr)
            results.append({'name': name, 'expected': 'PASS' if succeeds else 'FAIL',
                            'returncode': outcome.returncode, 'stdout': outcome.stdout, 'stderr': outcome.stderr,
                            'copy_bytes_unchanged_by_verifier': True})
    final = check(root)
    if final.returncode:
        raise RuntimeError('Original final preservation failed: ' + final.stderr)
    results.append({'name': 'original_after', 'expected': 'PASS', 'returncode': 0, 'stdout': final.stdout})
    result = {'artifact_controls': 'PASS', 'mathematical_test': False,
              'external_final': a.expected_final, 'external_report': a.expected_report,
              'disposable_cases': len(cases), 'cases': results,
              'original_preservation': 'Own sealed packet, all28 input originals and entire80-file actual author root verified before and after.'}
    out = work / 'controls-result.json'
    out.write_text(json.dumps(result, indent=2) + '\n')
    (work / 'controls-result.sha256').write_text(sha(out.read_bytes()) + '\n')
    print(json.dumps({'controls': 'PASS', 'disposable_cases': len(cases), 'original_checks': 2,
                      'result_sha256': sha(out.read_bytes())}, sort_keys=True))


if __name__ == '__main__':
    main()
