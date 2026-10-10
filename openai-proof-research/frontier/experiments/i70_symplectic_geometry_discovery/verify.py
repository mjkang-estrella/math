"""Read-only, offline I70 evidence verifier. Run with Python -B; stdout only.

Integrity and exact finite diagnostics are not certification of analytic proofs,
contribution, or completeness of a literature search. No acquisition is run.
The new seal excludes only itself and the captured verifier stdout; old seals
are never opened for modification. Four live ledgers may drift explicitly.
"""
from pathlib import Path
import collections
import hashlib
import json
import re
import runpy
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
SOURCE = ROOT / 'frontier/sources/i70_symplectic_geometry_discovery'
EXPERIMENT = Path(__file__).resolve().parent
REPORT = ROOT / 'frontier/iterations/i70-symplectic-geometry-discovery.md'
CORPUS = ROOT / 'frontier/sources/i14_spectral_width_novelty_r3/corpus'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
EXCLUDED = {SOURCE / 'seal-final.json', EXPERIMENT / 'verification.json'}
LEDGERS = {'README.md', 'frontier/README.md', 'frontier/TEN-FINDINGS.md',
           'frontier/iterations/README.md'}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def read(name):
    return json.loads((SOURCE / name).read_text())


def require(condition, label):
    if not condition:
        raise AssertionError(label)


def check_bytes(path, record, size_key='size'):
    data = path.read_bytes()
    require(sha(data) == record['sha256'], 'SHA256 mismatch: ' + str(path))
    require(len(data) == record[size_key], 'Size mismatch: ' + str(path))
    return data


def main():
    counters = {}
    seal = read('seal-final.json')
    actual = {REPORT}
    for directory in (SOURCE, EXPERIMENT):
        actual.update(p for p in directory.rglob('*') if p.is_file())
    actual -= EXCLUDED
    recorded = [ROOT / item['path'] for item in seal['files']]
    require(len(set(recorded)) == len(recorded), 'Duplicate seal entries')
    require(set(recorded) == actual, 'New seal file membership drift')
    for item in seal['files']:
        check_bytes(ROOT / item['path'], item)
    counters['sealed_artifacts'] = len(recorded)

    history = read('verification-development.json')
    first_seal = read(history['first_seal'])
    require(sha((SOURCE / history['first_seal']).read_bytes()) == history['first_seal_sha256'],
            'Original first seal changed')
    changed = {x['path']: x for x in history['changed_files']}
    actual_first_drift = set()
    for item in first_seal['files']:
        path = ROOT / item['path']
        if sha(path.read_bytes()) != item['sha256']:
            actual_first_drift.add(item['path'])
            require(item['path'] in changed, 'Unexplained drift since first I70 seal')
            old = (SOURCE / changed[item['path']]['old_bytes_snapshot']).read_bytes()
            require(sha(old) == item['sha256'] == changed[item['path']]['old_sha256'],
                    'First-seal old-byte snapshot mismatch')
    require(actual_first_drift == set(changed), 'First-seal drift accounting mismatch')
    counters['explained_first_seal_changed_files'] = len(changed)

    inputs = read('frozen-inputs.json')['files']
    require({x['path'] for x in inputs if x['mutable']} == LEDGERS,
            'Mutable-ledger classification changed')
    drifts = []
    for item in inputs:
        if item['snapshot']:
            check_bytes(SOURCE / item['snapshot'], item)
        path = ROOT / item['path']
        if item['mutable']:
            current = sha(path.read_bytes()) if path.exists() else None
            if current != item['sha256']:
                drifts.append({'path': item['path'], 'frozen_sha256': item['sha256'],
                               'live_sha256': current})
        else:
            check_bytes(path, item)
    counters['immutable_references'] = sum(not x['mutable'] for x in inputs)
    counters['mutable_ledgers'] = len(LEDGERS)

    require(read('inputs/sources/upstream.json')['commit'] == PIN, 'Pin changed')
    tree = read('inputs/sources/preprints-tree.json')
    require(not tree.get('truncated', False), 'Truncated catalogue')
    entries = tree['tree']
    require(len(entries) == 13223, 'Complete-tree count mismatch')
    titles = [x['path'] for x in entries if x['type'] == 'tree' and x['path'].count('/') == 1]
    require(len(titles) == 749, 'Complete manuscript count mismatch')
    blobs = {x['path']: x for x in entries if x['type'] == 'blob'}
    counters.update(catalogue_entries=len(entries), catalogue_manuscripts=len(titles))
    inventory = read('corpus-inventory.json')
    actual_paths = subprocess.check_output(['rg', '--files', '--no-ignore'], cwd=CORPUS,
                                           text=True).splitlines()
    require(collections.Counter(actual_paths) == collections.Counter(x['path'] for x in inventory),
            'Fixed corpus file multiset drift')
    require(len(inventory) == 9340, 'Corpus count mismatch')
    for item in inventory:
        data = check_bytes(CORPUS / item['path'], item)
        require(blob(data) == item['git_blob'] == blobs[item['path']]['sha'],
                'Corpus Git blob mismatch: ' + item['path'])
    counters['corpus_files'] = len(inventory)

    pin_manifest = read('pins.json')
    require(pin_manifest['commit'] == PIN, 'Pinned file revision mismatch')
    pins = pin_manifest['files'] + read('supplementary-pins.json')
    overlaps = sorted(set(x['path'] for x in pin_manifest['files']) &
                      set(x['path'] for x in read('supplementary-pins.json')))
    require(overlaps == history['overlapping_records'], 'Pinned provenance overlap drift')
    for item in pins:
        data = check_bytes(SOURCE / 'pinned' / item['path'], item)
        require(blob(data) == item['git_blob'] == blobs[item['path']]['sha'],
                'Pinned Git blob mismatch: ' + item['path'])
        require(item['raw_url'] == f'https://raw.githubusercontent.com/openai/math/{PIN}/' + item['path'],
                'Unpinned source URL: ' + item['path'])
        if item.get('response'):
            require(read(item['response'])['url'] == item['raw_url'], 'Supplement response mismatch')
    counters['retained_pinned_files'] = len({x['path'] for x in pins})
    counters['pinned_provenance_records'] = len(pins)

    searches = read('searches.json')
    require(ROOT / searches['domain'] == CORPUS and searches['domain_files'] == 9340,
            'Search domain mismatch')
    lengths = {}
    for item in searches['searches']:
        require(item['argv'][:7] == ['rg', '--no-ignore', '--line-number', '--with-filename',
                                     '--color', 'never', '-e'] and item['argv'][-1] == '.',
                'Unexpected search command')
        result = subprocess.run(item['argv'], cwd=CORPUS, text=True, capture_output=True, check=False)
        require(result.returncode == item['returncode'], 'Search exit-code drift')
        require(result.stderr == item['stderr'], 'Search stderr drift')
        require(collections.Counter(result.stdout.splitlines()) == collections.Counter(item['lines']),
                'Search line MULTISET drift: ' + item['name'])
        lengths[item['name']] = len(item['lines'])
    counters['search_line_multisets'] = lengths

    # Loading this module defines functions only. Its network main/get are NOT called.
    extraction = runpy.run_path(str(EXPERIMENT / 'acquire_primary.py'))['extract']
    response_count = extraction_count = raw_count = 0
    for path in sorted((SOURCE / 'primary').glob('*.json')):
        item = json.loads(path.read_text())
        data = check_bytes(path.parent / item['body'], item, 'bytes')
        require(item['status'] == 200, 'Archived HTTP retrieval was unsuccessful: ' + str(path))
        require(bool(item.get('requested_utc')) and bool(item.get('headers')), 'Missing HTTP provenance')
        if 'text' in item:
            text_bytes = (path.parent / item['text']).read_bytes()
            require(sha(text_bytes) == item['text_sha256'], 'Extracted text hash mismatch')
            require(extraction(data).encode() == text_bytes, 'HTML extraction replay mismatch')
            extraction_count += 1
        prefix = f'https://raw.githubusercontent.com/openai/math/{PIN}/'
        if item['url'].startswith(prefix):
            rel = item['url'][len(prefix):]
            require(data == (SOURCE / 'pinned' / rel).read_bytes(), 'Raw response/pin mismatch')
            require(blob(data) == blobs[rel]['sha'], 'Raw response Git blob mismatch')
            raw_count += 1
        response_count += 1
    counters.update(http_responses=response_count, html_extraction_replays=extraction_count,
                    fresh_pinned_raw_responses=raw_count)

    versions = read('current-versions.json')
    for item in versions:
        path = SOURCE / item['abs_body']
        require(sha(path.read_bytes()) == item['abs_sha256'], 'Version-page hash mismatch')
        observed = re.findall(re.escape(item['arxiv']) + r'v(\d+)', path.read_text())
        require(max(map(int, observed)) == item['latest_observed'], 'Latest observed version mismatch')
        expected = f"primary/{item['arxiv']}v{item['latest_observed']}-html.body"
        require(item['versioned_body'] == expected and (SOURCE / expected).is_file(),
                'Missing observed version body')
        start = item['history_first_line'] - 1
        lines = path.with_suffix('.txt').read_text().splitlines()
        require(lines[start:start + len(item['history_lines'])] == item['history_lines'],
                'Submission-history excerpt drift')
    counters['current_primary_version_observations'] = len(versions)

    passages = read('passages.json') + read('supplementary-passages.json')
    for item in passages:
        data = (SOURCE / item['path']).read_bytes()
        require(sha(data) == item['file_sha256'], 'Passage source hash mismatch')
        lines = data.decode().splitlines(keepends=True)
        require(1 <= item['first_line'] <= item['last_line'] <= len(lines), 'Invalid passage range')
        text = ''.join(lines[item['first_line'] - 1:item['last_line']])
        require(text == item['text'] and sha(text.encode()) == item['passage_sha256'],
                'Actual passage bytes mismatch')
    counters['exact_passages'] = len(passages)

    diagnostics = runpy.run_path(str(EXPERIMENT / 'diagnostics.py'))['run']()
    require(diagnostics == read('diagnostic-results.json'), 'Finite diagnostic reproduction mismatch')
    counters['finite_assertions'] = diagnostics['total_assertions']
    link_count = 0
    for target in re.findall(r'\]\(([^)]+)\)', REPORT.read_text()):
        if target.startswith(('https://', 'http://', '#')):
            continue
        require((REPORT.parent / target).exists(), 'Report local link missing: ' + target)
        link_count += 1
    counters['report_local_links'] = link_count
    result = {'status': 'PASS_EVIDENCE', 'counters': counters, 'mutable_ledger_drift': drifts,
              'analytic_status': 'Author proofs of technical partials; strongest RP unproved and unrefuted.',
              'contribution_status': 'No substantial nomination; no count increment.',
              'scope': 'Offline retained-byte integrity and finite reproduction, not universal theorem certification.',
              'failures': []}
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print(json.dumps({'status': 'FAIL_EVIDENCE', 'failure': type(error).__name__ + ': ' + str(error)},
                         indent=2, sort_keys=True))
        raise SystemExit(1)
