#!/usr/bin/env python3
"""Run integrity controls on disposable copies only. No mathematical tests."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys


def sha(data):
    return hashlib.sha256(data).hexdigest()


def put(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def snapshot(root, excluded=None):
    result = {}
    for path in [root] + sorted(root.rglob('*')):
        if excluded is not None and (path == excluded or excluded in path.parents):
            continue
        info = path.lstat()
        item = {'mode': stat.S_IMODE(info.st_mode), 'kind': 'dir' if path.is_dir() else 'file'}
        if path.is_file():
            data = path.read_bytes()
            item.update(bytes=len(data), sha256=sha(data))
        result[path.relative_to(root).as_posix()] = item
    return result


def reseal(case):
    """Artificial new detached anchors, explicitly only for semantic negative controls."""
    packet = case / 'packet'
    old = json.loads((packet / 'MANIFEST.json').read_text())
    for name, value in old['files'].items():
        path = packet / name
        data = path.read_bytes()
        value.update(sha256=sha(data), bytes=len(data), mode=stat.S_IMODE(path.stat().st_mode))
    put(packet / 'MANIFEST.json', old)
    final = json.loads((case / 'FINAL.json').read_text())
    final['manifest_sha256'] = sha((packet / 'MANIFEST.json').read_bytes())
    for name in final['payload_anchors']:
        final['payload_anchors'][name] = sha((packet / name).read_bytes())
    put(case / 'FINAL.json', final)
    return sha((case / 'FINAL.json').read_bytes()), sha((case / 'REPORT.md').read_bytes())


def repair_input_record(case, local):
    path = case / 'packet/private/input-register.json'
    records = json.loads(path.read_text())
    data = (case / 'packet' / local).read_bytes()
    for record in records:
        if record['local'] == local:
            record.update(sha256=sha(data), bytes=len(data))
    put(path, records)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--out', required=True, help='new single directory name under root')
    parser.add_argument('--finalhash', required=True)
    parser.add_argument('--reporthash', required=True)
    args = parser.parse_args()
    root = args.root.absolute()
    if args.out in ('', '.', '..') or '/' in args.out or '\\' in args.out:
        raise ValueError('out must be a new single directory name')
    out = root / args.out
    verifier = root / 'packet/public/verify.py'

    def run(case, finalhash, reporthash):
        proc = subprocess.run([sys.executable, '-B', str(verifier), '--root', str(case),
                               '--finalhash', finalhash, '--reporthash', reporthash],
                              capture_output=True, text=True)
        return {'returncode': proc.returncode, 'stdout': json.loads(proc.stdout), 'stderr': proc.stderr}

    pristine = run(root, args.finalhash, args.reporthash)
    if pristine['returncode'] != 0:
        raise ValueError('refusing controls on unauthenticated original: ' + str(pristine))
    out.mkdir(exist_ok=False)
    before = snapshot(root, out)
    results = []
    kinds = ['pristine-copy', 'wrong-final-anchor', 'wrong-report-anchor', 'changed-review',
             'missing-source', 'extra-file', 'extra-directory', 'symlink-source',
             'hardlink-source', 'changed-mode', 'changed-packet-root-mode',
             'reanchored-source-corruption', 'reanchored-status-corruption',
             'reanchored-verdict-corruption']
    for number, kind in enumerate(kinds):
        case = out / ('case-' + str(number))
        case.mkdir()
        shutil.copytree(root / 'packet', case / 'packet')
        for name in ('FINAL.json', 'REPORT.md'):
            shutil.copyfile(root / name, case / name)
        fh, rh = args.finalhash, args.reporthash
        sources = json.loads((case / 'packet/private/source-register.json').read_text())
        local = sources[0]['local']
        source = case / 'packet' / local
        if kind == 'wrong-final-anchor':
            fh = '0' * 64
        elif kind == 'wrong-report-anchor':
            rh = '0' * 64
        elif kind == 'changed-review':
            with (case / 'packet/public/review.md').open('a') as stream:
                stream.write('\nCONTROL MUTATION\n')
        elif kind == 'missing-source':
            source.unlink()
        elif kind == 'extra-file':
            (case / 'packet/unlisted.txt').write_text('control')
        elif kind == 'extra-directory':
            (case / 'packet/unlisted-empty').mkdir()
        elif kind == 'symlink-source':
            source.unlink()
            source.symlink_to(case / 'packet/public/review.md')
        elif kind == 'hardlink-source':
            backup = case / 'link-target'
            source.rename(backup)
            os.link(backup, source)
        elif kind == 'changed-mode':
            source.chmod(0o400)
        elif kind == 'changed-packet-root-mode':
            (case / 'packet').chmod(0o700)
        elif kind == 'reanchored-source-corruption':
            with source.open('a') as stream:
                stream.write('\n% CONTROL MUTATION\n')
            repair_input_record(case, local)
            sources[0]['sha256'] = sha(source.read_bytes())
            put(case / 'packet/private/source-register.json', sources)
            fh, rh = reseal(case)
        elif kind == 'reanchored-status-corruption':
            local = 'private/handoff/task-status.json'
            status_path = case / 'packet' / local
            status = json.loads(status_path.read_text())
            status['summary'] = 'altered terminal summary'
            put(status_path, status)
            repair_input_record(case, local)
            fh, rh = reseal(case)
        elif kind == 'reanchored-verdict-corruption':
            final_path = case / 'FINAL.json'
            final = json.loads(final_path.read_text())
            final['verdict'] = 'FAIL'
            put(final_path, final)
            fh = sha(final_path.read_bytes())
        observed = run(case, fh, rh)
        expected = 0 if kind == 'pristine-copy' else 1
        results.append({'case': kind, 'expected_returncode': expected, 'observed': observed,
                        'passed': observed['returncode'] == expected,
                        'artificial_reanchoring': kind.startswith('reanchored-')})
        shutil.rmtree(case)
    after = snapshot(root, out)
    unchanged = before == after
    receipt = {'status': 'COPIED_INTEGRITY_CONTROLS_ONLY', 'cases': results,
               'all_expected': all(item['passed'] for item in results),
               'original_review_files_and_modes_unchanged': unchanged,
               'preexisting_inventory_sha256': sha(json.dumps(before, sort_keys=True).encode()),
               'detached_FINAL': args.finalhash, 'detached_REPORT': args.reporthash,
               'disposable_copies_removed': True, 'mathematical_evidence': False}
    put(out / 'receipt.json', receipt)
    print(json.dumps({'receipt': str(out / 'receipt.json'), 'cases': len(results),
                      'all_expected': receipt['all_expected'], 'original_unchanged': unchanged,
                      'receipt_sha256': sha((out / 'receipt.json').read_bytes())}, sort_keys=True))
    return 0 if receipt['all_expected'] and unchanged else 1


if __name__ == '__main__':
    sys.exit(main())
