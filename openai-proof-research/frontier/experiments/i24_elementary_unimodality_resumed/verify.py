"""Offline read-only verifier. Integrity success is not proof acceptance."""
from pathlib import Path
import hashlib
import json
import subprocess

ROOT = Path(__file__).resolve().parents[3]
SOURCE = ROOT/'frontier/sources/i24_elementary_unimodality_resumed'
EXPERIMENT = ROOT/'frontier/experiments/i24_elementary_unimodality_resumed'
OLD = ROOT/'frontier/sources/i24_elementary_unimodality'
OLD_EXP = ROOT/'frontier/experiments/i24_elementary_unimodality'
REPORT = ROOT/'frontier/iterations/i24-elementary-unimodality-resumed.md'


def sha(b):
    return hashlib.sha256(b).hexdigest()


def read(path):
    return json.loads(path.read_text())


def verify_row(path, row):
    b = path.read_bytes()
    assert sha(b) == row['sha256'], f'Hash mismatch: {path}'
    assert len(b) == row['bytes'], f'Length mismatch: {path}'


def verify_slices(rows):
    for row in rows:
        p = ROOT/row['path']
        assert sha(p.read_bytes()) == row['file_sha256'], p
        text = '\n'.join(p.read_text().split('\n')[row['first_line']-1:row['last_line']])
        assert text == row['text'] and sha(text.encode()) == row['slice_sha256'], row['label']


def main():
    checkpoint = read(SOURCE/'inputs/frontier/experiments/i24-interrupted-checkpoint.json')
    oldpaths = {str(p.relative_to(ROOT)) for directory in (OLD, OLD_EXP)
                for p in directory.rglob('*') if p.is_file()}
    assert oldpaths == set(checkpoint['files']), 'Old tree file set changed'
    for name, row in checkpoint['files'].items():
        verify_row(ROOT/name, row)
    assert not (ROOT/'frontier/iterations/i24-elementary-unimodality.md').exists(), 'Historical no-report state changed'
    frozen = read(SOURCE/'inputs.json')
    shared_drift, workflow_drift, dependency_drift = [], [], []
    for row in frozen:
        path = SOURCE/'inputs'/row['path']
        verify_row(path, row)
        current = ROOT/row['path']
        if not current.exists() or sha(current.read_bytes()) != row['sha256']:
            if row['path'] == 'frontier/TEN-FINDINGS.md':
                shared_drift.append(row['path'])
            elif row['path'].endswith('-task.json') and current.exists() and read(current)['brief'] == read(path)['brief']:
                workflow_drift.append(row['path'])
            else:
                dependency_drift.append(row['path'])
    assert not dependency_drift, ('Non-shared dependency drift', dependency_drift)
    # Earlier shared state may differ from current snapshots. Keep that separate.
    inherited_input_drift = []
    for row in read(OLD/'inputs.json'):
        verify_row(OLD/'inputs'/row['path'], row)
        path = ROOT/row['path']
        if not path.exists() or sha(path.read_bytes()) != row['sha256']:
            inherited_input_drift.append(row['path'])
    assert all(p == 'frontier/TEN-FINDINGS.md' for p in inherited_input_drift), inherited_input_drift
    pinned = read(SOURCE/'pinned-references.json')
    assert pinned['pin'] == 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
    tree = read(ROOT/pinned['complete_tree'])
    assert not tree['truncated']
    entries = {r['path']: r for r in tree['tree']}
    directories = {r['path'].split('/')[1] for r in tree['tree']
                   if r['path'].startswith('preprints/') and len(r['path'].split('/')) > 2}
    assert len(directories) == pinned['manuscript_directories'] == 749
    for row in pinned['files']:
        path = ROOT/row['local_path']
        verify_row(path, row)
        b = path.read_bytes()
        blob = hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        assert blob == row['git_blob'] == entries[row['path']]['sha'], row['path']
        assert row['url'] == 'https://raw.githubusercontent.com/openai/math/'+pinned['pin']+'/'+row['path']
    source_contracts = read(SOURCE/'source-contracts.json')
    passages = read(SOURCE/'read-locators.json')['passages']
    primary = read(SOURCE/'primary-contracts.json')
    verify_slices(source_contracts)
    verify_slices(passages)
    verify_slices(primary)
    literature = read(OLD/'literature/manifest.json')
    for row in literature:
        verify_row(OLD/'literature'/row['file'], row)
    extracted = read(SOURCE/'pdf-text-verification.json')
    for row in extracted:
        assert row['exact_extraction_match']
        b = subprocess.run(['pdftotext', '-layout', str(ROOT/row['pdf']), '-'],
                           capture_output=True, check=True).stdout
        assert b == (ROOT/row['text']).read_bytes() and sha(b) == row['extracted_sha256'], row['pdf']
    seal = read(EXPERIMENT/'artifact-seal.json')
    for row in seal['artifacts']:
        verify_row(ROOT/row['path'], row)
    actual = {str(p.relative_to(ROOT)) for d in (SOURCE, EXPERIMENT) for p in d.rglob('*') if p.is_file()}
    actual.add(str(REPORT.relative_to(ROOT)))
    actual.remove(str((EXPERIMENT/'artifact-seal.json').relative_to(ROOT)))
    assert actual == {r['path'] for r in seal['artifacts']}, 'Unsealed new artifacts or missing files'
    state = read(SOURCE/'completed-state.json')
    assert state['status'] == 'COMPLETED_SCOPED_GAP'
    assert state['target_proved'] is False and state['count_increment'] == 0
    print(json.dumps({'integrity': 'PASS', 'mathematical_acceptance': 'NOT ASSERTED',
          'sealed_artifacts': len(seal['artifacts']), 'inherited_files_unchanged': len(checkpoint['files']),
          'new_frozen_inputs': len(frozen), 'pinned_sources': len(pinned['files']),
          'source_contracts': len(source_contracts), 'read_passages': len(passages),
          'primary_contracts': len(primary), 'primary_retrievals': len(literature),
          'pdf_text_pairs': len(extracted), 'live_shared_index_drift': shared_drift,
          'historical_shared_input_drift': inherited_input_drift,
          'workflow_record_drift_same_brief': workflow_drift,
          'non_shared_dependency_drift': dependency_drift}, indent=2))


if __name__ == '__main__':
    main()
