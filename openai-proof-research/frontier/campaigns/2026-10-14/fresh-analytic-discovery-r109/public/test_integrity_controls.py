#!/usr/bin/env python3
"""Exercise verifier on packet copies only. Original code: MIT.
Run before the final seal; writes private/integrity-controls.json after cleanup.
"""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).absolute().parent.parent
RECEIPT = 'private/integrity-controls.json'

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def original_state():
    return {p.relative_to(ROOT).as_posix(): digest(p) for p in ROOT.rglob('*') if p.is_file() and p.relative_to(ROOT).as_posix() not in {RECEIPT, 'manifest.json'}}

def seal(root):
    files = []
    dirs = []
    for p in sorted(root.rglob('*')):
        name = p.relative_to(root).as_posix()
        if p.is_dir():
            dirs.append(name)
        elif name != 'manifest.json':
            files.append({'path': name, 'bytes': p.stat().st_size, 'sha256': digest(p)})
    files.sort(key=lambda item: item['path'])
    dirs.sort()
    manifest = {'schema': 'exact-inventory-v1', 'claim': 'evidence integrity only; no mathematical certification', 'files': files, 'directories': dirs}
    (root/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
    return digest(root/'manifest.json')

def edit_manifest(root, action):
    path = root/'manifest.json'
    data = json.loads(path.read_text())
    action(data)
    path.write_text(json.dumps(data, indent=2)+'\n')
    return digest(path)

def main():
    before = original_state()
    cases = []
    with tempfile.TemporaryDirectory(prefix='.integrity-work-', dir=ROOT) as tmp:
        work = Path(tmp)
        base = work/'baseline'
        for name in before:
            destination = base/name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT/name, destination)
        base_anchor = seal(base)
        for name in ['positive', 'no-anchor', 'wrong-anchor', 'modified-bytes', 'missing-file', 'extra-file', 'extra-directory', 'file-symlink', 'directory-symlink', 'duplicate-path', 'traversal-path', 'duplicate-json-key', 'bad-length-type', 'freeze-mismatch']:
            root = work/name
            shutil.copytree(base, root)
            anchor = base_anchor
            target = root/'public/frozen-target.md'
            if name == 'wrong-anchor': anchor = '0'*64
            elif name == 'modified-bytes': target.write_bytes(target.read_bytes()+b'\nchanged\n')
            elif name == 'missing-file': target.unlink()
            elif name == 'extra-file': (root/'extra').write_text('extra')
            elif name == 'extra-directory': (root/'extra').mkdir()
            elif name == 'file-symlink':
                target.unlink(); target.symlink_to('../README.md')
            elif name == 'directory-symlink': (root/'linked-directory').symlink_to('private', target_is_directory=True)
            elif name == 'duplicate-path': anchor = edit_manifest(root, lambda d: d['files'].append(d['files'][0].copy()))
            elif name == 'traversal-path': anchor = edit_manifest(root, lambda d: d['files'][0].update(path='../escape'))
            elif name == 'duplicate-json-key':
                p=root/'manifest.json'; p.write_text(p.read_text().replace('"schema":', '"schema":"exact-inventory-v1", "schema":', 1)); anchor=digest(p)
            elif name == 'bad-length-type': anchor = edit_manifest(root, lambda d: d['files'][0].update(bytes=True))
            elif name == 'freeze-mismatch':
                p=root/'scope-freeze.json'; data=json.loads(p.read_text()); data['sha256']='0'*64; p.write_text(json.dumps(data)); anchor=seal(root)
            command=[sys.executable, str(root/'public/verify_inventory.py'), '--root', str(root)]
            if name != 'no-anchor': command += ['--manifest-sha256', anchor]
            result=subprocess.run(command, capture_output=True, text=True)
            expected_accept = name == 'positive'
            assert (result.returncode == 0) == expected_accept, (name, result.stdout, result.stderr)
            cases.append({'case': name, 'expected_accept': expected_accept, 'exit_code': result.returncode, 'observed': result.stdout.strip() if expected_accept else result.stderr.strip().splitlines()[-1]})
    assert original_state() == before, 'original file bytes changed during controls'
    receipt={'scope': 'full available preseal packet copied; final receipt and final manifest not included in copy', 'copied_baseline_manifest_sha256':base_anchor, 'original_file_count_unchanged':len(before), 'original_bytes_unchanged':True, 'frozen_target_sha256':digest(ROOT/'public/frozen-target.md'), 'cases':cases, 'preliminary_failure':'Initial copied positive control rejected unsorted file inventory; Path ordering was replaced by explicit POSIX-path lexical sorting before this run.', 'claim':'integrity controls only; not mathematical validation'}
    (ROOT/RECEIPT).write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps({'cases':len(cases), 'all_expected_outcomes':True, 'original_bytes_unchanged':True}))

if __name__ == '__main__':
    main()
