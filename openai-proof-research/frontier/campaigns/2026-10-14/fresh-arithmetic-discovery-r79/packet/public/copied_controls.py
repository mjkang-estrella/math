#!/usr/bin/env python3
"""MIT; Myeongjin Kang. Copy-only integrity controls, never mathematical gates."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def digest(b):
    return hashlib.sha256(b).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', type=Path, required=True)
    ap.add_argument('--finalhash', required=True,
                    help='Trusted detached FINAL SHA256; never inferred from the packet')
    args = ap.parse_args()
    root = args.root.resolve()
    if root != Path(__file__).resolve().parents[2]:
        raise ValueError('run the controls from the owned original packet')
    verifier = root / 'packet/public/verify.py'
    cases = []

    def inventory():
        return {p.relative_to(root).as_posix(): digest(p.read_bytes())
                for p in sorted((root / 'packet').rglob('*')) if p.is_file()} | {
                n: digest((root / n).read_bytes())
                for n in ('FINAL.json', 'MANIFEST.json', 'REPORT.md')}

    before = inventory()

    def run(name, target, expected, anchor=args.finalhash, missing=False):
        # Use the original verifier for every copy, not executable bytes in a mutated copy.
        cmd = [sys.executable, '-B', str(verifier), '--root', str(target)]
        if not missing:
            cmd += ['--finalhash', anchor]
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
        passed = (result.returncode == 0) == expected
        cases.append(dict(name=name, expected_accept=expected,
                          returncode=result.returncode, control_passed=passed,
                          stdout=result.stdout.strip(), stderr=result.stderr.strip()))
        if not passed:
            raise ValueError('unexpected control result: ' + name)

    run('original_external_anchor_positive', root, True)
    with tempfile.TemporaryDirectory(prefix='copy-r79-', dir=root / 'integrity') as temp:
        copy = Path(temp)
        shutil.copytree(root / 'packet', copy / 'packet')
        for name in ('FINAL.json', 'MANIFEST.json', 'REPORT.md'):
            shutil.copyfile(root / name, copy / name)
        run('copy_external_anchor_positive', copy, True)
        run('wrong_finalhash', copy, False, anchor='0' * 64)
        run('missing_finalhash', copy, False, missing=True)

        def changed(name, path, replacement):
            old = path.read_bytes()
            path.write_bytes(replacement)
            try:
                run(name, copy, False)
            finally:
                path.write_bytes(old)

        p = copy / 'packet/public/research.md'
        changed('changed_research', p, p.read_bytes() + b'changed\n')
        old = p.read_bytes()
        p.unlink()
        try:
            run('missing_packet_member', copy, False)
        finally:
            p.write_bytes(old)
        p = copy / 'packet/public/extra.txt'
        p.write_text('extra')
        run('extra_packet_member', copy, False)
        p.unlink()
        p = copy / 'packet/public/extra-dir'
        p.mkdir()
        run('extra_empty_directory', copy, False)
        p.rmdir()
        p = copy / 'packet/public/link.txt'
        p.symlink_to('research.md')
        run('symlink_file', copy, False)
        p.unlink()
        p = copy / 'packet/private/link-dir'
        p.symlink_to('../public', target_is_directory=True)
        run('symlink_directory', copy, False)
        p.unlink()
        for name in ('MANIFEST.json', 'REPORT.md', 'FINAL.json'):
            p = copy / name
            changed('changed_' + name, p, p.read_bytes() + b' ')
        p = next((copy / 'packet/private/upstream').rglob('02-reduction.tex'))
        changed('changed_canonical_source', p, p.read_bytes() + b'% changed\n')
        p = copy / 'packet/private/primary/vaisman-math0106070v1.pdf'
        changed('changed_primary', p, p.read_bytes() + b'changed\n')

        # Rehash an altered report into a coherent new FINAL. The old external
        # anchor must still reject it; merely matching local files is not enough.
        p = copy / 'REPORT.md'
        f = copy / 'FINAL.json'
        old_report, old_final = p.read_bytes(), f.read_bytes()
        p.write_bytes(old_report + b'forged report\n')
        forged = json.loads(old_final)
        forged['report_sha256'] = digest(p.read_bytes())
        f.write_text(json.dumps(forged, indent=2, sort_keys=True) + '\n')
        try:
            run('rehash_report_and_final_old_external_anchor', copy, False)
        finally:
            p.write_bytes(old_report)
            f.write_bytes(old_final)

        # Rehash a changed public member, manifest, and FINAL together. This
        # stronger local forgery is also defeated by the external FINAL hash.
        p = copy / 'packet/public/research.md'
        m = copy / 'MANIFEST.json'
        old_public, old_manifest, old_final = p.read_bytes(), m.read_bytes(), f.read_bytes()
        p.write_bytes(old_public + b'forged public bytes\n')
        forged_manifest = json.loads(old_manifest)
        for entry in forged_manifest['files']:
            if entry['path'] == 'public/research.md':
                entry.update(bytes=len(p.read_bytes()), sha256=digest(p.read_bytes()))
        m.write_text(json.dumps(forged_manifest, indent=2, sort_keys=True) + '\n')
        forged_final = json.loads(old_final)
        forged_final['manifest_sha256'] = digest(m.read_bytes())
        f.write_text(json.dumps(forged_final, indent=2, sort_keys=True) + '\n')
        try:
            run('rehash_member_manifest_final_old_external_anchor', copy, False)
        finally:
            p.write_bytes(old_public)
            m.write_bytes(old_manifest)
            f.write_bytes(old_final)
        run('restored_copy_positive', copy, True)

    run('original_after_copied_controls', root, True)
    after = inventory()
    if before != after:
        raise ValueError('original packet or anchor/report files changed')
    receipt = dict(kind='COPY_ONLY_INTEGRITY_CONTROLS', detached_finalhash=args.finalhash,
                   cases=cases, all_passed=all(c['control_passed'] for c in cases),
                   original_packet_unchanged=True,
                   original_inventory_sha256=digest(json.dumps(before, sort_keys=True).encode()),
                   mathematical_gate=False)
    output = root / 'integrity/controls.json'
    output.write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
    print(json.dumps(dict(cases=len(cases), all_passed=receipt['all_passed'],
                         original_packet_unchanged=True, controls_sha256=digest(output.read_bytes()),
                         detached_finalhash=args.finalhash), sort_keys=True))


if __name__ == '__main__':
    main()
