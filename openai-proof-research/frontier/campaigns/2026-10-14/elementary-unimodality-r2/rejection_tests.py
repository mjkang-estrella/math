#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT License.
"""Disposable-copy integrity controls; writes only inside the assigned directory."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def state(root):
    values = []
    for p in sorted(root.rglob('*')):
        if p.is_file():
            raw = p.read_bytes()
            values.append((str(p.relative_to(root)), len(raw), sha(raw)))
    return sha(json.dumps(values, separators=(',', ':')).encode())


def reseal_failed_checker(copy):
    path = copy/'checks.py'
    path.write_text("raise RuntimeError('deliberate authenticated checker failure')\n")
    manifest_path = copy/'outputs-manifest.json'
    manifest = json.loads(manifest_path.read_bytes())
    for entry in manifest['files']:
        if entry['path'] == 'checks.py':
            raw = path.read_bytes()
            entry.update(size=len(raw), sha256=sha(raw))
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True)+'\n')
    seal_path = copy/'seal.json'
    seal = json.loads(seal_path.read_bytes())
    raw = manifest_path.read_bytes()
    seal['manifests']['outputs-manifest.json'].update(size=len(raw), sha256=sha(raw))
    seal_path.write_text(json.dumps(seal, indent=2, sort_keys=True)+'\n')
    anchor = sha(seal_path.read_bytes())
    (copy/'seal.sha256').write_text(anchor+'  seal.json\n')
    return anchor


def main():
    root = Path(__file__).resolve().parent
    r8 = root.parent/'fresh-structural-discovery-r8'
    before = state(root), state(r8)
    files = [p.relative_to(root) for p in root.rglob('*') if p.is_file()]
    anchor = sha((root/'seal.json').read_bytes())
    results = []
    with tempfile.TemporaryDirectory(prefix='.rejection-', dir=root) as temporary:
        for name in ('candidate_corruption', 'missing_source', 'authenticated_checker_failure'):
            copy = Path(temporary)/name
            copy.mkdir()
            for rel in files:
                destination = copy/rel
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(root/rel, destination)
            test_anchor = anchor
            if name == 'candidate_corruption':
                (copy/'candidate.md').write_bytes((copy/'candidate.md').read_bytes()+b'corruption\n')
            elif name == 'missing_source':
                (copy/'inputs/private/upstream/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/README.md').unlink()
            else:
                test_anchor = reseal_failed_checker(copy)
            copied_before = state(copy)
            run = subprocess.run([sys.executable, '-I', '-B', '-S', str(copy/'verify.py'),
                                  '--seal', test_anchor, '--r8', str(r8)],
                                 cwd=copy, capture_output=True, timeout=120, check=False)
            if run.returncode != 1 or run.stderr:
                raise RuntimeError('unexpected rejection result: '+name)
            result = json.loads(run.stdout)
            if result['status'] != 'REJECTED' or not result['trees_unchanged'] or copied_before != state(copy):
                raise RuntimeError('rejection control mutated/failed: '+name)
            if name == 'authenticated_checker_failure' and not result['reason'].startswith('authenticated checker failed'):
                raise RuntimeError('failure-path test did not execute authenticated failing checker')
            results.append({'control': name, 'rejected': True, 'copy_unchanged': True})
    if before != (state(root), state(r8)):
        raise RuntimeError('original package or frozen r8 changed')
    print(json.dumps({'controls': results, 'original_trees_unchanged': True,
                      'scope': 'Integrity rejection controls only; full U UNRESOLVED'}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
