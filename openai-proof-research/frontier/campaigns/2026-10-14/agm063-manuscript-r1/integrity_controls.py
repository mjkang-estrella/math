#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. SPDX-License-Identifier: MIT
"""Exercise the real verifier against a complete isolated snapshot and real tampering.
Writes only below this owned package; never alters a sealed source packet.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from seal import make_manifest
from verify import MANIFEST, inventory, need, sha

ROOT = Path(__file__).absolute().parent


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--final-ready', action='store_true')
    args = ap.parse_args()
    need(not (ROOT / MANIFEST).exists(), 'run controls before sealing')
    files, dirs = inventory(ROOT)
    before = {p: sha((ROOT / p).read_bytes()) for p in files}
    records = []
    with tempfile.TemporaryDirectory(prefix='.integrity-work-', dir=ROOT) as tmp:
        work = Path(tmp)
        copy = work / 'copy'
        copy.mkdir()
        for name in dirs:
            (copy / name).mkdir(parents=True, exist_ok=True)
        for name in files:
            shutil.copyfile(ROOT / name, copy / name)
        mp = copy / MANIFEST
        mp.write_text(json.dumps(make_manifest(copy, 'final' if args.final_ready else 'preseal-control'), indent=2) + '\n')
        baseline = mp.read_bytes()
        anchor = sha(baseline)

        def run(name, ok=False, given=None, at=None, contains=None):
            command = [sys.executable, '-B', str(copy / 'verify.py'), '--anchor',
                       anchor if given is None else given, '--root', str(copy if at is None else at)]
            proc = subprocess.run(command, capture_output=True, text=True)
            need((proc.returncode == 0) == ok, 'unexpected control result: ' + name)
            need(not proc.stderr, 'unexpected verifier stderr: ' + name)
            if contains:
                need(contains in proc.stdout, 'wrong rejection reason: ' + name)
            records.append({'control': name, 'expected_accept': ok, 'exit_code': proc.returncode,
                            'stdout': proc.stdout.strip(), 'stderr': proc.stderr})

        run('unchanged-full-snapshot', True)
        run('wrong-external-anchor', given='0' * 64, contains='external anchor mismatch')
        source = copy / 'main.tex'
        original = source.read_bytes()
        source.write_bytes(original + b'\n% genuine tamper\n')
        run('changed-main', contains='payload mismatch: main.tex')
        source.write_bytes(original)
        source.unlink()
        run('missing-main', contains='exact file membership')
        source.write_bytes(original)
        (copy / 'unexpected.txt').write_text('unexpected\n')
        run('extra-file', contains='exact file membership')
        (copy / 'unexpected.txt').unlink()
        (copy / 'unexpected-directory').mkdir()
        run('extra-empty-directory', contains='exact directory membership')
        (copy / 'unexpected-directory').rmdir()
        source.unlink()
        source.symlink_to(ROOT / 'main.tex')
        run('payload-symlink', contains='symlink: main.tex')
        source.unlink()
        source.write_bytes(original)
        (copy / 'linked-directory').symlink_to(ROOT / 'private', target_is_directory=True)
        run('directory-symlink', contains='symlink: linked-directory')
        (copy / 'linked-directory').unlink()
        root_link = work / 'root-link'
        root_link.symlink_to(copy, target_is_directory=True)
        run('root-symlink', at=root_link, contains='symlink in root ancestry')
        root_link.unlink()
        outside = work / 'manifest-bytes.json'
        outside.write_bytes(baseline)
        mp.unlink()
        mp.symlink_to(outside)
        run('manifest-symlink', contains='symlink: output-manifest.json')
        mp.unlink()
        mp.write_bytes(baseline)
        outside.unlink()
        os.link(source, copy / 'hardlink.tex')
        run('hard-linked-payload', contains='hard-linked file:')
        (copy / 'hardlink.tex').unlink()
        os.mkfifo(copy / 'unexpected-fifo')
        run('nonregular-fifo', contains='nonregular file:')
        (copy / 'unexpected-fifo').unlink()

        # These changed manifests get separate caller-supplied test anchors, so
        # failures exercise schema/path checks rather than the outer hash check.
        duplicate = baseline.decode().replace('{', '{"schema":"duplicate",', 1).encode()
        mp.write_bytes(duplicate)
        run('duplicate-json-key', given=sha(duplicate), contains='duplicate JSON key')
        mp.write_bytes(baseline)
        for name, change, reason in [
            ('traversal-path', lambda m: m['files'][0].update(path='../outside'), 'noncanonical path'),
            ('absolute-path', lambda m: m['files'][0].update(path='/outside'), 'noncanonical path'),
            ('duplicate-payload-record', lambda m: m['files'].append(m['files'][0]), 'duplicate/self payload'),
            ('duplicate-directory-record', lambda m: m['directories'].append(m['directories'][0]), 'directory inventory order/duplicates'),
        ]:
            m = json.loads(baseline)
            change(m)
            mp.write_text(json.dumps(m))
            run(name, given=sha(mp.read_bytes()), contains=reason)
            mp.write_bytes(baseline)
        source.write_bytes(original + b'\n% locally rehashed attack\n')
        m = json.loads(baseline)
        row = next(r for r in m['files'] if r['path'] == 'main.tex')
        row.update(bytes=source.stat().st_size, sha256=sha(source.read_bytes()))
        mp.write_text(json.dumps(m))
        run('payload-and-manifest-rehash-with-old-external-anchor', contains='external anchor mismatch')
        source.write_bytes(original)
        mp.write_bytes(baseline)
        if args.final_ready:
            for label, name, mutate, reason in [
                ('stale-source-build-binding', 'checks/build-receipt.json',
                 lambda x: x.update(source_sha256='0' * 64), 'build binding: source_sha256'),
                ('stale-visual-pdf-binding', 'checks/visual-review.json',
                 lambda x: x.update(pdf_sha256='0' * 64), 'visual PDF binding'),
                ('missing-root-formal-adoption', 'final-checkpoint.json',
                 lambda x: x.update(formal_review_adopted_by_root=False), 'formal adoption pending'),
            ]:
                target = copy / name
                saved = target.read_bytes()
                data = json.loads(saved)
                mutate(data)
                target.write_text(json.dumps(data))
                m = json.loads(baseline)
                row = next(r for r in m['files'] if r['path'] == name)
                row.update(bytes=target.stat().st_size, sha256=sha(target.read_bytes()))
                mp.write_text(json.dumps(m))
                run(label, given=sha(mp.read_bytes()), contains=reason)
                target.write_bytes(saved)
                mp.write_bytes(baseline)
        run('restored-full-snapshot', True)
        need({p: sha((copy / p).read_bytes()) for p in files} == before,
             'snapshot restoration failed')
    after_files, after_dirs = inventory(ROOT)
    need(after_files == files and after_dirs == dirs and
         {p: sha((ROOT / p).read_bytes()) for p in files} == before,
         'original package changed during controls')
    report = {'status': 'PASS_REAL_ISOLATED_TAMPER_CONTROLS',
              'stage': 'final-ready' if args.final_ready else 'preseal',
              'snapshot_manifest_sha256': anchor, 'snapshot_file_count': len(files),
              'snapshot_directory_count': len(dirs),
              'verifier_sha256': before['verify.py'], 'main_sha256': before['main.tex'],
              'original_before_after_identical': True, 'controls': records,
              'limits': 'No final seal or mathematical verdict is created by these controls.'}
    (ROOT / 'checks/integrity-controls.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'status': report['status'], 'controls': len(records),
                      'original_before_after_identical': True}))


if __name__ == '__main__':
    main()
