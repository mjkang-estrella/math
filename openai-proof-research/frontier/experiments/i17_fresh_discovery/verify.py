"""Verify frozen inputs, pinned sources, exact contracts, and the handoff seal."""
from pathlib import Path
import hashlib
import json
import sys
from datetime import datetime, timezone

BASE = Path(__file__).resolve().parents[3]
SRC = BASE / 'frontier/sources/i17_fresh_discovery'
EXP = BASE / 'frontier/experiments/i17_fresh_discovery'
REPORT = BASE / 'frontier/iterations/i17-fresh-discovery.md'
errors = []
counts = {}
live_changes = []


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read(name):
    return json.loads((SRC / name).read_text())


def check(condition, message):
    if not condition:
        errors.append(message)


def filecheck(path, digest, size=None):
    p = BASE / path
    if not p.is_file():
        errors.append('Missing: ' + path)
        return b''
    data = p.read_bytes()
    check(sha(data) == digest, 'SHA256 mismatch: ' + path)
    if size is not None:
        check(len(data) == size, 'Size mismatch: ' + path)
    return data


for item in read('input-snapshots.json'):
    filecheck(item['snapshot'], item['sha256'], item['bytes'])
    live = BASE / item['path']
    if not live.is_file() or sha(live.read_bytes()) != item['sha256']:
        live_changes.append(item['path'])
counts['input_snapshots'] = len(read('input-snapshots.json'))
inventory = json.loads((SRC / 'inputs/sources/preprints-tree.json').read_text())
check(inventory['truncated'] is False, 'Frozen inventory is truncated')
entries = {x['path']: x for x in inventory['tree']}
counts['inventory_entries'] = len(entries)
screen = read('complete-inventory-screen.json')
check(screen['all_entries'] == inventory['tree'], 'Inventory screen differs from frozen complete tree')

pinned = read('pinned-manifest.json')
by_local = {x['local']: x for x in pinned}
revision = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
for item in pinned:
    data = filecheck(item['local'], item['sha256'], item['bytes'])
    blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    check(blob == item['git_blob'] == entries[item['path']]['sha'], 'Git blob mismatch: ' + item['path'])
    check(item['url'] == 'https://raw.githubusercontent.com/openai/math/' + revision + '/' + item['path'], 'Unpinned URL: ' + item['path'])
counts['pinned_git_blobs'] = len(pinned)

contracts = read('theorem-contracts.json')
for item in contracts:
    lines = (BASE / item['local']).read_text().splitlines(keepends=True)
    passage = ''.join(lines[item['start_line'] - 1:item['end_line']])
    check(item['exact_statement'] in passage, 'Statement range mismatch: ' + str(item['labels']))
    check(sha(item['exact_statement'].encode()) == item['statement_sha256'], 'Statement hash mismatch: ' + str(item['labels']))
    check(item['git_blob'] == by_local[item['local']]['git_blob'], 'Statement source mismatch')
counts['exact_statement_contracts'] = len(contracts)
for item in read('read-ranges.json'):
    lines = (BASE / item['local']).read_text().splitlines(keepends=True)
    passage = ''.join(lines[item['start_line'] - 1:item['end_line']])
    check(sha(passage.encode()) == item['range_sha256'], 'Read range mismatch: ' + item['local'])
    check(item['git_blob'] == by_local[item['local']]['git_blob'], 'Read range source mismatch')
counts['selected_read_ranges'] = len(read('read-ranges.json'))

literature = read('literature/manifest.json')
for item in literature:
    filecheck(item['file'], item['sha256'])
    filecheck(item['text_file'], item['text_sha256'])
counts['primary_literature_retrievals'] = len(literature)
for item in read('primary-statement-contracts.json'):
    source = (BASE / item['text_file']).read_text()
    passage = source[item['start_char']:item['end_char']]
    check(passage == item['exact_statement'], 'Primary statement offset mismatch: ' + item['label'])
    check(sha(passage.encode()) == item['statement_sha256'], 'Primary statement hash mismatch: ' + item['label'])
counts['primary_statement_contracts'] = len(read('primary-statement-contracts.json'))
latest = read('literature/latest-upstream-comparison.json')
check(latest['status'] == 'COMPLETE', 'Incomplete latest prior-art comparison')
for item in latest['files']:
    data = filecheck(item['file'], item['sha256'])
    blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    check(blob == item['git_blob'], 'Latest prior-art blob mismatch')
counts['latest_prior_art_blobs'] = len(latest['files'])
for name in ['diagnostics.json', 'series-diagnostics.json']:
    result = json.loads((EXP / name).read_text())
    check(result['status'] == 'PASS', 'Diagnostic failure: ' + name)

seal = read('artifact-manifest.json')
for item in seal['files']:
    filecheck(item['path'], item['sha256'], item['bytes'])
excluded = {SRC / 'artifact-manifest.json', SRC / 'verification.json'}
actual = {str(p.relative_to(BASE)) for root in (SRC, EXP) for p in root.rglob('*') if p.is_file() and p not in excluded}
actual.add(str(REPORT.relative_to(BASE)))
check(actual == {x['path'] for x in seal['files']}, 'Artifact file set differs from sealed file set')
counts['sealed_artifacts'] = len(seal['files'])
result = dict(status='FAIL' if errors else 'PASS', checked_utc=datetime.now(timezone.utc).isoformat(),
              counts=counts, errors=errors, live_inputs_changed_since_freeze=live_changes,
              live_change_policy='Informational only; frozen premises remain verified.',
              artifact_manifest_sha256=sha((SRC / 'artifact-manifest.json').read_bytes()),
              report_sha256=sha(REPORT.read_bytes()))
(SRC / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
sys.exit(bool(errors))
