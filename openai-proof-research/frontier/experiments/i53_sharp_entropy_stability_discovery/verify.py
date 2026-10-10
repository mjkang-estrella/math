"""Offline, read-only evidence replay. This verifies records, not the theorem."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
S = Path('frontier/sources/i53_sharp_entropy_stability_discovery')
E = Path('frontier/experiments/i53_sharp_entropy_stability_discovery')
REPORT = Path('frontier/iterations/i53-sharp-entropy-stability-discovery.md')
CORPUS = Path('frontier/sources/i14_spectral_width_novelty_r3/corpus')
MUTABLE = {'README.md', 'frontier/README.md', 'frontier/TEN-FINDINGS.md',
           'frontier/iterations/README.md'}
failures, drift, counts = [], [], {}


def check(condition, message):
    if not condition:
        failures.append(message)


def read(path):
    return (ROOT / path).read_bytes()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def record(path):
    return json.loads(read(path))


def run(args):
    return subprocess.run(args, cwd=ROOT, capture_output=True,
                          env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})


def verify():
    seal = record(S / 'seal.json')
    exclusions = {str(S / 'seal.json'), str(S / 'verification.json')}
    actual = {str(REPORT)}
    for directory in (S, E):
        actual.update(str(p.relative_to(ROOT)) for p in (ROOT / directory).rglob('*')
                      if p.is_file() and str(p.relative_to(ROOT)) not in exclusions)
    check(actual == set(seal['files']), 'sealed artifact inventory differs')
    for path, digest in seal['files'].items():
        check(sha(read(path)) == digest, 'artifact digest: ' + path)
    counts['sealed_artifacts'] = len(seal['files'])

    inputs = record(S / 'inputs.json')
    for item in inputs:
        check(sha(read(item['frozen'])) == item['sha256'], 'frozen input: ' + item['path'])
        if sha(read(item['path'])) != item['sha256']:
            if item['path'] in MUTABLE:
                drift.append(item['path'])
            else:
                failures.append('immutable live input drift: ' + item['path'])
    counts['frozen_inputs'] = len(inputs)

    tree = record(S / 'inputs/sources/preprints-tree.json')
    check(not tree.get('truncated', False), 'complete tree marked truncated')
    blobs = {x['path']: x['sha'] for x in tree['tree'] if x['type'] == 'blob'}
    counts['complete_tree_entries'] = len(tree['tree'])
    pins = record(S / 'pinned-manifest.json')
    for item in pins:
        data = read(S / 'pinned' / item['path'])
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        check(blob == item['git_blob'] == blobs.get(item['path']), 'pinned Git blob: ' + item['path'])
        check(sha(data) == item['sha256'], 'pinned SHA256: ' + item['path'])
        check('/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in item['url'], 'unpinned source URL')
    counts['pinned_blobs'] = len(pins)

    inventory = record(S / 'corpus-inventory.json')
    result = run(['rg', '--files', '--no-ignore', str(CORPUS)])
    check(result.returncode == 0 and not result.stderr, 'corpus inventory rg failure')
    paths = sorted(str(Path(p).relative_to(CORPUS)) for p in result.stdout.decode().splitlines())
    check(paths == sorted(item[0] for item in inventory), 'full corpus path inventory')
    for path, digest in inventory:
        check(sha(read(CORPUS / path)) == digest, 'corpus file: ' + path)
    counts['corpus_files'] = len(inventory)

    searches = record(S / 'searches.json')
    counts['corpus_search_line_multisets'] = {}
    for item in searches:
        result = run(['rg', '--no-ignore', '-n', '-i', item['pattern'], str(CORPUS)])
        check(result.returncode == item['returncode'], 'search return code: ' + item['name'])
        check(result.stderr.decode() == item['stderr'], 'search stderr: ' + item['name'])
        lines = sorted(result.stdout.decode().splitlines())
        check(lines == record(S / (item['name'] + '-multiset.json')), 'search multiset: ' + item['name'])
        check(len(lines) == item['hits'], 'search multiplicity: ' + item['name'])
        counts['corpus_search_line_multisets'][item['name']] = len(lines)

    literature = record(S / 'literature/manifest.json')
    extracted = 0
    for item in literature:
        if 'path' in item:
            check(sha(read(item['path'])) == item['sha256'], 'primary response: ' + item['name'])
        extraction = item.get('text_extraction')
        if extraction and extraction.get('sha256'):
            check(sha(read(extraction['path'])) == extraction['sha256'], 'primary text: ' + item['name'])
            if item['path'].endswith('.pdf'):
                result = run(['pdftotext', '-layout', item['path'], '-'])
                check(result.returncode == extraction['returncode'], 'PDF extraction status: ' + item['name'])
                check(result.stdout == read(extraction['path']), 'PDF text replay: ' + item['name'])
                extracted += 1
    counts['primary_requests'] = len(literature)
    counts['pdf_text_replays'] = extracted

    passages = record(S / 'passages.json')
    for item in passages:
        lines = read(item['path']).decode().splitlines(keepends=True)
        check(1 <= item['first_line'] <= item['last_line'] <= len(lines), 'passage range: ' + item['path'])
        data = ''.join(lines[item['first_line'] - 1:item['last_line']]).encode()
        check(sha(data) == item['sha256'], 'passage digest: ' + item['path'])
    counts['proof_passages'] = len(passages)

    result = run([sys.executable, str(E / 'diagnostics.py')])
    check(result.returncode == 0 and not result.stderr, 'diagnostics process')
    check(result.stdout == read(E / 'diagnostics.json'), 'deterministic diagnostics replay')
    counts['diagnostic_assertions'] = json.loads(result.stdout)['total_assertions']


try:
    verify()
except Exception as exc:
    failures.append(type(exc).__name__ + ': ' + str(exc))
print(json.dumps({'status': 'PASS' if not failures else 'FAIL', 'counts': counts,
                  'mutable_ledger_drift_informational': drift, 'failures': failures,
                  'scope': 'Evidence integrity and finite diagnostics; not an independent universal proof review.'},
                 indent=2, sort_keys=True))
sys.exit(bool(failures))
