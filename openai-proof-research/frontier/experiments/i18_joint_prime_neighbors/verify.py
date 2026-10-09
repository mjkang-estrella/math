"""Verify I18's frozen research packet; no network or git mutations.

--seal is an explicit authoring operation, to be used only after edits/review.
The default verifies the existing seal; it never silently blesses edits.
Live input drift is reported separately, since the parent may work concurrently.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import importlib.util
import json
import sys

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[3]
SRC = ROOT / 'frontier/sources/i18_joint_prime_neighbors'
EXP = Path(__file__).resolve().parent
REPORT = ROOT / 'frontier/iterations/i18-joint-prime-neighbors.md'
SEAL = SRC / 'artifact-seal.json'
VALIDATION = EXP / 'validation.json'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def relative(path):
    return str(path.relative_to(ROOT))


def packet_paths():
    # Reading check.py via exec_module can create __pycache__; those runtime
    # products are not research artifacts and are explicitly excluded.
    return sorted({REPORT} | {
        p for directory in (SRC, EXP) for p in directory.rglob('*')
        if p.is_file() and p not in (SEAL, VALIDATION)
        and '__pycache__' not in p.parts
    })


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--seal', action='store_true')
    args = parser.parse_args()
    errors, drift = [], []
    manifest = json.loads((SRC / 'manifest.json').read_text())
    tree_row = next(r for r in manifest['inputs'] if r['path'] == 'sources/preprints-tree.json')
    tree = json.loads((ROOT / tree_row['frozen_path']).read_text())
    if tree.get('truncated'):
        errors.append('Frozen preprint tree is truncated')
    git_ids = {r['path']: r['sha'] for r in tree['tree'] if r['type'] == 'blob'}
    for row in manifest['inputs']:
        data = (ROOT / row['frozen_path']).read_bytes()
        if digest(data) != row['sha256'] or len(data) != row['bytes']:
            errors.append('Frozen input mismatch: ' + row['path'])
        live = ROOT / row['path']
        if not live.exists() or digest(live.read_bytes()) != row['sha256']:
            drift.append(row['path'])
    for row in manifest['pinned']:
        data = (ROOT / row['local_path']).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if digest(data) != row['sha256'] or len(data) != row['bytes']:
            errors.append('Pinned bytes mismatch: ' + row['path'])
        if blob != row['git_blob'] or git_ids.get(row['path']) != blob:
            errors.append('Pinned tree identity mismatch: ' + row['path'])
        wanted = 'https://raw.githubusercontent.com/openai/math/' + manifest['pin'] + '/' + row['path']
        if row['url'] != wanted:
            errors.append('Nonpinned URL: ' + row['path'])
    literature = json.loads((SRC / 'literature/manifest.json').read_text())
    for row in literature:
        data = (ROOT / row['path']).read_bytes()
        if digest(data) != row['sha256'] or len(data) != row['bytes']:
            errors.append('Literature mismatch: ' + row['path'])
    contracts = json.loads((SRC / 'source-contracts.json').read_text())
    for row in contracts['sources']:
        path = ROOT / row['local_path']
        data = path.read_bytes()
        if digest(data) != row['sha256']:
            errors.append('Contract source hash mismatch: ' + row['local_path'])
        for first, last in row['read_ranges']:
            if not (1 <= first <= last <= len(data.splitlines())):
                errors.append('Invalid read range: ' + row['local_path'])
    spec = importlib.util.spec_from_file_location('i18_diagnostics', EXP / 'check.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    computed = module.run()
    stored = json.loads((EXP / 'results.json').read_text())
    if computed != stored:
        errors.append('Diagnostic output differs on rerun')
    if args.seal:
        if errors:
            raise SystemExit('Cannot seal invalid inputs: ' + repr(errors))
        rows = []
        for path in packet_paths():
            data = path.read_bytes()
            rows.append({'path': relative(path), 'sha256': digest(data), 'bytes': len(data)})
        SEAL.write_text(json.dumps({
            'scope': 'I18 only; excludes this seal, validation.json, runtime __pycache__',
            'created_utc': datetime.now(timezone.utc).isoformat(),
            'artifacts': rows,
        }, indent=2) + '\n')
    seal = json.loads(SEAL.read_text())
    expected_paths = {row['path'] for row in seal['artifacts']}
    if expected_paths != {relative(p) for p in packet_paths()}:
        errors.append('Artifact set differs from sealed set')
    for row in seal['artifacts']:
        path = ROOT / row['path']
        if not path.exists():
            errors.append('Missing sealed artifact: ' + row['path'])
            continue
        data = path.read_bytes()
        if digest(data) != row['sha256'] or len(data) != row['bytes']:
            errors.append('Sealed artifact mismatch: ' + row['path'])
    result = {
        'checked_utc': datetime.now(timezone.utc).isoformat(),
        'status': 'PASS' if not errors else 'FAIL',
        'mathematical_scope': 'Identity diagnostics and integrity only, not independent proof review',
        'pinned_files': len(manifest['pinned']), 'frozen_inputs': len(manifest['inputs']),
        'primary_literature_files': len(literature),
        'source_contract_files': len(contracts['sources']),
        'sealed_artifacts': len(seal['artifacts']),
        'seal_sha256': digest(SEAL.read_bytes()),
        'diagnostics': computed['counts'],
        'live_input_drift': drift, 'errors': errors,
    }
    VALIDATION.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
    raise SystemExit(bool(errors))


if __name__ == '__main__':
    main()
