"""Read-only, offline I69 evidence replay; not an analytic theorem verifier.

Provenance scaffolding adapted transparently from I65; I69 diagnostics are independent.
No network, writes, imports of author diagnostic modules, prior seal refresh,
or modification of shared ledgers. Run from any directory. The optional
--skip-seal flag is deliberately absent: a public replay always checks the seal.
"""
from collections import Counter
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
SRC = ROOT / 'frontier/sources/i69_global_algebra_rounding_budget'
EXP = ROOT / 'frontier/experiments/i69_global_algebra_rounding_budget'
REPORT = ROOT / 'frontier/iterations/i69-global-algebra-rounding-budget.md'
CORPUS = ROOT / 'frontier/sources/i14_spectral_width_novelty_r3/corpus'
SHA = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
MUTABLE = {'README.md', 'frontier/README.md', 'frontier/TEN-FINDINGS.md',
           'frontier/iterations/README.md'}

def require(condition, message):
    if not condition:
        raise AssertionError(message)

def digest(b):
    return hashlib.sha256(b).hexdigest()

def blob(b):
    return hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()

def read_json(p):
    return json.loads(p.read_bytes())

def checked_path(path):
    p = ROOT / path
    require(p.resolve().is_relative_to(ROOT), 'Path escapes project: ' + path)
    return p

def hashed_file(path, sha):
    p = checked_path(path)
    b = p.read_bytes()
    require(digest(b) == sha, 'Hash mismatch: ' + path)
    return b

def command(args):
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    return subprocess.run(args, cwd=ROOT, env=env, capture_output=True)

def main():
    out = {'status': 'PASS', 'scope': 'Offline provenance and finite diagnostics only; '
           'not universal theorem, novelty, acceptance, or live-version verification.'}
    seal = read_json(SRC / 'seal.json')
    require(seal['pinned_commit'] == SHA, 'Seal pin')
    expected = {r['path']: r['sha256'] for r in seal['files']}
    excluded = {SRC / 'seal.json', SRC / 'verification.json'}
    actual = {str(p.relative_to(ROOT)) for base in [SRC, EXP]
              for p in base.rglob('*') if p.is_file() and p not in excluded}
    actual.add(str(REPORT.relative_to(ROOT)))
    require(actual == set(expected), 'I69 sealed file-set mismatch')
    for p, sha in expected.items():
        hashed_file(p, sha)
    out['sealed_artifacts'] = len(expected)

    inputs = read_json(SRC / 'inputs.json')
    require({r['path'] for r in inputs if r['mutable']} == MUTABLE, 'Mutable allowlist')
    drift = []
    for r in inputs:
        frozen = SRC / 'inputs' / r['path']
        require(digest(frozen.read_bytes()) == r['sha256'], 'Frozen input: ' + r['path'])
        same = digest(checked_path(r['path']).read_bytes()) == r['sha256']
        if r['mutable']:
            if not same:
                drift.append(r['path'])
        else:
            require(same, 'Immutable live input drift: ' + r['path'])
    task = read_json(SRC / 'inputs/frontier/iterations/iteration69-global-algebra-rounding-budget-task.json')
    require((SRC / 'brief.txt').read_text() == task['brief'], 'Exact full brief')
    require(read_json(SRC / 'inputs/sources/upstream.json')['commit'] == SHA, 'Upstream pin')
    out['frozen_inputs'] = len(inputs)
    out['allowed_live_ledger_drift'] = sorted(drift)

    prior = read_json(SRC / 'prior-hashes.json')
    require(len({r['path'] for r in prior}) == len(prior), 'Duplicate prior path')
    for r in prior:
        hashed_file(r['path'], r['sha256'])
    out['prior_hash_references'] = len(prior)

    tree = read_json(SRC / 'inputs/sources/preprints-tree.json')
    require(tree['truncated'] is False and len(tree['tree']) == 13223, 'Complete tree')
    manuscripts = {r['path'].split('/')[1] for r in tree['tree']}
    require(len(manuscripts) == 749, 'Manuscript count')
    tree_blobs = {r['path']: r['sha'] for r in tree['tree'] if r['type'] == 'blob'}
    inventory = read_json(SRC / 'corpus.json')
    cp = str(CORPUS.relative_to(ROOT))
    listing = command(['rg', '--files', '--no-ignore', cp])
    require(listing.returncode == 0, 'Corpus listing failed')
    listed = {str(Path(p).relative_to(cp)) for p in listing.stdout.decode().splitlines()}
    require(len(inventory) == 9340 and listed == {r['path'] for r in inventory}, 'Corpus set')
    require(len(tree_blobs) == 10373 and listed <= set(tree_blobs), 'Corpus belongs to complete tree')
    outside = read_json(SRC / 'tree-outside-corpus.json')
    require(len(outside) == 1033 and outside == [r for r in tree['tree']
            if r['type'] == 'blob' and r['path'] not in listed], 'Tree entries outside fixed corpus')
    for r in inventory:
        b = (CORPUS / r['path']).read_bytes()
        require(digest(b) == r['sha256'], 'Corpus sha256: ' + r['path'])
        require(blob(b) == r['git_blob'] == tree_blobs[r['path']], 'Corpus Git blob: ' + r['path'])
    out.update(tree_entries=13223, tree_blobs=10373, manuscripts=749,
               corpus_blobs=9340, tree_blobs_outside_fixed_corpus=1033)

    pins = read_json(SRC / 'pins.json')
    for r in pins:
        b = checked_path(r['local_path']).read_bytes()
        require(digest(b) == r['sha256'], 'Pinned sha256: ' + r['path'])
        require(blob(b) == r['git_blob'] == tree_blobs[r['path']], 'Pinned Git blob: ' + r['path'])
        require(r['url'] == 'https://raw.githubusercontent.com/openai/math/' + SHA + '/' + r['path'], 'Pinned URL')
    out['pinned_files'] = len(pins)

    searches = read_json(SRC / 'searches.json')
    counts = {}
    for r in searches:
        p = command(['rg', '--no-ignore', '-n', r['pattern'], cp])
        require(p.returncode == r['returncode'], 'Search status: ' + r['name'])
        require(p.stderr.decode() == r['stderr'], 'Search stderr: ' + r['name'])
        saved = read_json(SRC / (r['name'] + '-search.json'))
        require(Counter(p.stdout.decode().splitlines()) == Counter(saved), 'Search multiset: ' + r['name'])
        require(len(saved) == r['count'], 'Search count: ' + r['name'])
        counts[r['name']] = len(saved)
    out['search_line_multisets'] = counts

    primary = read_json(SRC / 'primary/manifest.json')
    pdfs = 0
    failures = []
    for r in primary:
        if 'error' in r:
            failures.append({'name': r['name'], 'error': r['error']})
            continue
        b = hashed_file(r['path'], r['sha256'])
        require(len(b) == r['bytes'] and r['status'] == 200, 'HTTP record: ' + r['name'])
        if 'text_path' in r:
            text_bytes = hashed_file(r['text_path'], r['text_sha256'])
            p = command(['pdftotext', '-layout', r['path'], '-'])
            require(p.returncode == r['extract_returncode'] == 0, 'PDF status: ' + r['name'])
            require(p.stdout == text_bytes, 'PDF text replay: ' + r['name'])
            require(p.stderr.decode() == r['extract_stderr'], 'PDF warning provenance: ' + r['name'])
            pdfs += 1
    out['primary_successful_responses'] = len(primary) - len(failures)
    out['primary_failures'] = failures
    out['pdf_replays'] = pdfs

    passages = read_json(SRC / 'passages.json')
    for r in passages:
        b = hashed_file(r['path'], r['file_sha256'])
        piece = b''.join(b.splitlines(keepends=True)[r['first_line']-1:r['last_line']])
        require(digest(piece) == r['passage_sha256'] and piece.decode() == r['text'], 'Passage: ' + r['path'])
    contracts = read_json(SRC / 'read-contracts.json')
    for r in contracts['inputs']:
        b = (SRC / 'inputs' / r['path']).read_bytes()
        require(digest(b) == r['sha256'], 'Read-contract frozen hash')
        if r['read_scope'] == 'FULL':
            require(len(b.decode().splitlines()) == r['lines'], 'Read-contract length')
    out['frozen_source_passages'] = len(passages)
    versions = read_json(SRC / 'primary/versions.json')
    import re
    for r in versions:
        b = hashed_file(r['path'], r['sha256'])
        require(re.findall(r'arXiv:\s*[^\s\[]+', b.decode()[:5000]) == r['served_markers'], 'Version marker')
        require(b.decode().splitlines()[:15] == r['first_lines'], 'Version header')
    out['read_contracts'] = len(contracts['inputs'])
    old_replay = read_json(SRC / 'i65-readonly-replay.json')
    require(old_replay['status'] == 'PASS' and old_replay['sealed_artifacts'] == 98, 'Saved unchanged I65 replay')
    out['i65_replay'] = 'Saved separate unchanged PASS; provenance, not analytic premise'
    out['environment'] = read_json(SRC / 'environment.json')

    diag = command([sys.executable, '-B', str(EXP / 'diagnostics.py')])
    require(diag.returncode == 0 and not diag.stderr, 'Diagnostic process')
    require(diag.stdout == (SRC / 'diagnostics.json').read_bytes(), 'Diagnostic byte replay')
    d = json.loads(diag.stdout)
    out['exact_assertions'] = d['exact_assertions']
    out['floating_records'] = len(d['floating_records'])
    out['analytic_review'] = 'No independent full-proof acceptance claimed; see report.'
    print(json.dumps(out, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
