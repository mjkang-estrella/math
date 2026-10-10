#!/usr/bin/env python3
"""Offline, read-only I88 verifier. No fetching, writing, repair, or resealing."""
import collections
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
SRC = 'frontier/sources/i88_nonlinear_banach_discovery'
EXP = 'frontier/experiments/i88_nonlinear_banach_discovery'
REPORT = 'frontier/iterations/i88-nonlinear-banach-discovery.md'
SEAL = SRC + '/seal.json'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
DRIFT = {'README.md', 'frontier/README.md', 'frontier/TEN-FINDINGS.md', 'frontier/iterations/README.md'}


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read(path):
    return (ROOT / path).read_bytes()


def load(path):
    return json.loads(read(path))


def main():
    seal = load(SEAL)
    require(seal['pin'] == PIN, 'Wrong pin')
    require(seal['owned_directories'] == [SRC, EXP] and seal['owned_report'] == REPORT, 'Wrong owned domain')
    actual = {REPORT}
    for name in (SRC, EXP):
        for p in (ROOT / name).rglob('*'):
            require(not p.is_symlink(), 'Owned symlink: ' + str(p))
            if p.is_file():
                actual.add(p.relative_to(ROOT).as_posix())
    actual.discard(SEAL)
    records = seal['files']
    expected = {x['path'] for x in records}
    require(len(expected) == len(records) and actual == expected, 'Owned domain mismatch: ' + repr(actual ^ expected))
    for rec in records:
        b = read(rec['path'])
        require(len(b) == rec['bytes'] and digest(b) == rec['sha256'], 'Owned hash: ' + rec['path'])
    drift = []
    inputs = load(SRC + '/inputs.json')
    require({r['original'] for r in inputs if r['may_drift']} == DRIFT, 'Drift allowlist mismatch')
    for rec in inputs:
        require(digest(read(rec['snapshot'])) == rec['sha256'], 'Snapshot hash: ' + rec['snapshot'])
        current = digest(read(rec['original']))
        if current != rec['sha256']:
            require(rec['original'] in DRIFT and rec['may_drift'], 'Immutable input changed: ' + rec['original'])
            drift.append(rec['original'])
    for rec in load(SRC + '/immutable-references.json'):
        require(digest(read(rec['path'])) == rec['sha256'], 'Immutable reference changed: ' + rec['path'])
    require(PIN in read('sources/upstream.json').decode(), 'Upstream pin missing')
    print('Owned files, snapshots and immutable reference hashes PASS', flush=True)

    tree = load(SRC + '/snapshots/sources/preprints-tree.json')
    require(tree['truncated'] is False and len(tree['tree']) == 13223, 'Incomplete tree')
    blobs = {r['path']: r for r in tree['tree'] if r['type'] == 'blob'}
    domain = load(SRC + '/search-domain.json')
    by_path = {r['path']: r for r in domain}
    require(len(blobs) == len(domain) == len(by_path) == 10373 and set(blobs) == set(by_path), 'Blob domain mismatch')
    require(len({r['path'].split('/')[1] for r in domain}) == 749, 'Manuscript count mismatch')
    inherited = load('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json')
    inherited_by_path = {r['path']: r for r in inherited}
    require(set(inherited_by_path) == set(by_path), 'I79 search map domain mismatch')
    requests = [json.loads(line) for line in read('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside-requests.jsonl').splitlines()]
    outside = {r['path']: r for r in requests}
    require(len(outside) == len(requests) == 1033, 'Outside map mismatch')
    extracted = corpus = 0
    for i, rec in enumerate(domain, 1):
        path = rec['path']
        require(all(rec[key] == inherited_by_path[path][key] for key in ['path', 'local', 'kind', 'sha256']), 'I79 searchable provenance: ' + path)
        b = read(rec['original_local'])
        git_hash = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        require(git_hash == rec['git_sha'] == blobs[path]['sha'], 'Git blob mismatch: ' + path)
        require(digest(b) == rec['original_sha256'], 'Original body hash: ' + path)
        body = b if rec['original_local'] == rec['local'] else read(rec['local'])
        require(digest(body) == rec['sha256'], 'Search body hash: ' + path)
        if path in outside:
            r = outside[path]
            require(r['status'] == 200 and r['git_match'] and PIN in r['url'], 'Outside response provenance: ' + path)
            require(r['local'] == rec['original_local'] and r['sha256'] == rec['original_sha256'] and r['sha'] == git_hash, 'Outside original mapping: ' + path)
            if 'extraction' in r:
                require(r['extraction']['code'] == 0 and r['extraction']['path'] == rec['local'] and r['extraction']['sha256'] == rec['sha256'], 'Extraction mapping: ' + path)
                extracted += 1
        else:
            require(rec['kind'] == 'corpus', 'Unaccounted source body: ' + path)
            corpus += 1
        if i % 2000 == 0:
            print('Verified pinned bodies:', i, flush=True)
    require(corpus == 9340 and extracted == 776, 'Corpus/extraction count mismatch')
    corpus_actual = {p.relative_to(ROOT).as_posix() for p in (ROOT / 'frontier/sources/i14_spectral_width_novelty_r3/corpus').rglob('*') if p.is_file()}
    require(corpus_actual == {r['original_local'] for r in domain if r['kind'] == 'corpus'}, 'I14 file-domain drift')
    families = load(SRC + '/families.json')
    selected = load(SRC + '/selected-inventory.json')
    want_selected = [dict(r, alias=next(k for k, v in families.items() if v == r['path'].split('/')[1])) for r in domain if r['path'].split('/')[1] in families.values()]
    require(selected == want_selected, 'Selected family inventory mismatch')
    for rec in load(SRC + '/read-manifest.json'):
        original = by_path[rec['path']]
        require(rec['sha256'] == original['sha256'] and rec['local'] == original['local'], 'Read manifest reference mismatch')
    print('Complete pinned corpus and I79 provenance PASS', flush=True)

    queries = []
    for name in ['queries.json', 'queries-corrected.json', 'queries-final.json']:
        queries.extend(load(SRC + '/' + name))
    states = []
    for q in queries:
        require(q['flags'] == 'IGNORECASE', 'Unknown regex flags')
        states.append([q, re.compile(q['pattern'], re.I), hashlib.sha256(), 0, set()])
    for i, rec in enumerate(domain, 1):
        # Path.read_text uses universal newline conversion, matching discovery.
        lines = (ROOT / rec['local']).read_text(encoding='utf-8', errors='replace').splitlines()
        for line_number, line in enumerate(lines, 1):
            for state in states:
                q, pattern, hashed, count, manuscripts = state
                if pattern.search(line):
                    row = dict(path=rec['path'], local=rec['local'], line=line_number, text=line)
                    hashed.update((json.dumps(row, ensure_ascii=False) + '\n').encode())
                    state[3] += 1
                    manuscripts.add(rec['path'].split('/')[1])
        if i % 2000 == 0:
            print('Replayed full-domain searches through body:', i, flush=True)
    for q, pattern, hashed, count, manuscripts in states:
        require(count == q['records'] and len(manuscripts) == q['manuscripts'], 'Search count mismatch: ' + q['name'])
        require(hashed.hexdigest() == digest(read(SRC + '/search-' + q['name'] + '.jsonl')), 'Exact search multiset/order mismatch: ' + q['name'])
    print('All seven exact search result multisets PASS', flush=True)

    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    result = subprocess.run([sys.executable, str(ROOT / EXP / 'diagnostics.py')], cwd=ROOT, env=env, capture_output=True, check=True)
    require(result.stdout == read(EXP + '/diagnostics.json'), 'Diagnostic replay mismatch')
    for p in (ROOT / SRC / 'external').glob('*.response.json'):
        r = json.loads(p.read_bytes())
        require(r['status'] == 200, 'External response failed: ' + str(p))
        b = read(SRC + '/external/' + r['name'])
        require(len(b) == r['bytes'] and digest(b) == r['sha256'], 'External response-body hash mismatch')
        if 'text' in r:
            require(r['extraction_returncode'] == 0 and digest(read(r['text'])) == r['text_sha256'], 'External extraction mismatch')
    print(json.dumps(dict(status='EVIDENCE PASS', owned_files=len(records), pinned_blobs=len(domain), manuscripts=749,
                          corpus_files=corpus, pdf_extractions=extracted, search_queries=len(states),
                          allowed_ledger_drift=drift, diagnostics='PASS_FINITE_STRESS_TESTS_ONLY',
                          original_proof_review='NOT PERFORMED BY THIS VERIFIER',
                          contribution_verdict='NOT PERFORMED BY THIS VERIFIER; AUTHOR NOMINATES NO SUBSTANTIAL FINDING'), indent=2))


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print('EVIDENCE FAIL:', type(error).__name__ + ':', str(error), file=sys.stderr)
        sys.exit(1)
