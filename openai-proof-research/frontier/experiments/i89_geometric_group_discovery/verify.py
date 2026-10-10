#!/usr/bin/env python3
"""Offline READ-ONLY I89 evidence verifier. No fetch, repair, output file, or reseal.

Normal use checks the sealed exact owned domain. --preseal is a development
check that refuses to run once either seal file exists. It cannot create one.
Subprocesses are restricted to rg inventory, pdftotext to stdout, and the sealed
stdlib diagnostics under python -B. All comparisons occur in memory.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

sys.dont_write_bytecode = True
R = Path(__file__).resolve().parents[3]
S = 'frontier/sources/i89_geometric_group_discovery'
E = 'frontier/experiments/i89_geometric_group_discovery'
REPORT = 'frontier/iterations/i89-geometric-group-discovery.md'
SEAL = S + '/seal-v1.json'
ANCHOR = S + '/seal-v1.sha256'
OWNED_DIRS = [S, E]
EXCLUSIONS = [SEAL, ANCHOR]
MUTABLE = ['README.md', 'frontier/README.md', 'frontier/TEN-FINDINGS.md',
           'frontier/iterations/README.md']
I79 = 'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3'
CORPUS = 'frontier/sources/i14_spectral_width_novelty_r3/corpus'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def path(name):
    p = Path(name)
    require(not p.is_absolute() and '..' not in p.parts, 'unsafe path: ' + name)
    q = R
    for part in p.parts:
        q = q / part
        require(not q.is_symlink(), 'symlink: ' + str(q))
    return q


def raw(name):
    return path(name).read_bytes()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def gitsha(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def load(name):
    return json.loads(raw(name))


def lines(name):
    return [json.loads(s) for s in raw(name).decode().splitlines() if s]


def checkhash(name, digest):
    b = raw(name)
    require(sha(b) == digest, 'SHA-256 mismatch: ' + name)
    return b


def inventory():
    result = {REPORT}
    require(path(REPORT).is_file(), 'missing report')
    for directory in OWNED_DIRS:
        require(path(directory).is_dir(), 'missing owned directory')
        for p in path(directory).rglob('*'):
            name = p.relative_to(R).as_posix()
            path(name)  # reject any symlink even if it is not a regular file
            if p.is_file():
                result.add(name)
            else:
                require(p.is_dir(), 'nonregular owned artifact: ' + name)
    return result


def extract(pdf, txt):
    p = subprocess.run(['pdftotext', '-layout', str(path(pdf)), '-'],
                       cwd=R, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       check=False)
    require(p.returncode == 0, 'pdftotext failed: ' + pdf)
    require(p.stdout == raw(txt), 'PDF extraction mismatch: ' + txt)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--preseal', action='store_true')
    args = parser.parse_args()
    owned = inventory()
    if args.preseal:
        require(not path(SEAL).exists() and not path(ANCHOR).exists(),
                '--preseal forbidden after sealing')
    else:
        seal_bytes = raw(SEAL)
        require(raw(ANCHOR).decode() == sha(seal_bytes) + '  seal-v1.json\n',
                'seal anchor mismatch')
        seal = json.loads(seal_bytes)
        require(seal['version'] == 1 and seal['pin'] == PIN, 'seal identity')
        require(seal['owned_report'] == REPORT and seal['owned_directories'] == OWNED_DIRS,
                'wrong owned domain')
        require(seal['exclusions'] == EXCLUSIONS, 'wrong self-exclusions')
        require(seal['mutable_ledgers'] == MUTABLE, 'wrong mutable exceptions')
        files = seal['files']
        require(owned == set(files) | set(EXCLUSIONS),
                'owned domain mismatch; extra=' + str(sorted(owned-set(files)-set(EXCLUSIONS)))
                + '; missing=' + str(sorted(set(files)-owned)))
        for name, rec in files.items():
            b = checkhash(name, rec['sha256'])
            require(len(b) == rec['bytes'], 'owned size mismatch: ' + name)

    drift = []
    inputs = load(S + '/inputs.json')
    require({d['path'] for d in inputs} == set(MUTABLE) | {'AGENTS.md'}, 'snapshot domain')
    for d in inputs:
        require(d['mutable'] == (d['path'] in MUTABLE), 'illegal mutability')
        checkhash(d['snapshot'], d['sha256'])
        if sha(raw(d['path'])) != d['sha256']:
            require(d['mutable'], 'immutable input drift: ' + d['path'])
            drift.append(d['path'])
    references = load(S + '/immutable-references.json')
    require(len({d['path'] for d in references}) == len(references), 'duplicate references')
    for d in references:
        checkhash(d['path'], d['sha256'])
    require(PIN in raw('sources/upstream.json').decode(), 'wrong premise pin')

    tree = load('sources/preprints-tree.json')
    require(tree['truncated'] is False and len(tree['tree']) == 13223, 'tree scope')
    blobs = {d['path']: d for d in tree['tree'] if d['type'] == 'blob'}
    manuscripts = {p.split('/')[1] for p in blobs}
    require(len(blobs) == 10373 and len(manuscripts) == 749, 'blob/manuscript counts')
    domain = load(I79 + '/search-domain.json')
    require(len(domain) == 10373 and {d['path'] for d in domain} == set(blobs),
            'representative coverage')
    bypath = {d['path']: d for d in domain}
    outside = lines(I79 + '/outside-requests.jsonl')
    require(len(outside) == 1033, 'outside original count')
    outside_map = {d['path']: d for d in outside}
    require(len(outside_map) == 1033, 'duplicate outside originals')
    i79seal = {d['path']: d for d in load(I79 + '/seal-v1.json')['artifacts']}
    for name in [I79 + '/search-domain.json', I79 + '/outside-requests.jsonl']:
        require(sha(raw(name)) == i79seal[name]['sha256'], 'I79 seal binding: ' + name)

    n_pdf = 0
    for d in outside:
        require(d['status'] == 200 and d['git_match'] is True, 'outside response')
        b = checkhash(d['local'], d['sha256'])
        require(len(b) == d['bytes'] == blobs[d['path']]['size'], 'outside size')
        require(gitsha(b) == d['sha'] == blobs[d['path']]['sha'], 'outside git identity')
        require(sha(b) == i79seal[d['local']]['sha256'], 'original I79 binding')
        require(PIN in d['url'], 'outside request pin')
        representative = bypath[d['path']]
        if 'extraction' in d:
            n_pdf += 1
            x = d['extraction']
            require(x['code'] == 0 and representative['kind'] == 'outside_pdf', 'extraction status')
            require(representative['local'] == x['path'] and representative['sha256'] == x['sha256'],
                    'extraction representative mismatch')
            checkhash(x['path'], x['sha256'])
            require(x['sha256'] == i79seal[x['path']]['sha256'], 'extraction I79 binding')
        else:
            require(representative['local'] == d['local'] and representative['sha256'] == d['sha256'],
                    'non-PDF representative mismatch')
    require(n_pdf == 776, 'PDF original count')

    corpus = [d for d in domain if d['kind'] == 'corpus']
    require(len(corpus) == 9340, 'corpus count')
    require({d['path'] for d in corpus}.isdisjoint(outside_map), 'overlapping source domains')
    require({d['path'] for d in corpus} | set(outside_map) == set(blobs), 'original coverage')
    rg = subprocess.check_output(['rg', '--files', '--no-ignore', CORPUS], cwd=R)
    expected_files = raw(S + '/corpus-rg-files.txt').decode().splitlines()
    observed_files = rg.decode().splitlines()
    require(len(observed_files) == len(expected_files) == 9340, 'rg inventory size')
    require(sorted(observed_files) == sorted(expected_files) == sorted(d['local'] for d in corpus),
            'rg inventory multiset')

    queries = load(S + '/searches.json')
    require([q['name'] for q in queries] == ['ggt', 'effective_relative', 'fixed_energy'], 'search scope')
    patterns = [re.compile(q['pattern'], re.I) for q in queries]
    hits = [[] for q in queries]
    for d in domain:
        b = checkhash(d['local'], d['sha256'])
        if d['kind'] == 'corpus':
            require(gitsha(b) == blobs[d['path']]['sha'], 'corpus git identity: ' + d['path'])
            require(len(b) == blobs[d['path']]['size'], 'corpus size')
        for lineno, line in enumerate(b.decode(errors='replace').splitlines(), 1):
            for i, pat in enumerate(patterns):
                if pat.search(line):
                    hits[i].append({'path': d['path'], 'local': d['local'], 'line': lineno, 'text': line})
    for q, result in zip(queries, hits):
        require(q['flags'] == 'IGNORECASE', 'search flags')
        checkhash(q['output'], q['sha256'])
        require(len(result) == q['count'] and result == load(q['output']), 'search replay: ' + q['name'])

    families = ['Baumslag-Solitar-free', 'Virtual-compact-specialness', 'A-hyperbolic-group-with-no',
                'a-torsion-free-hyperbolic', 'Finite-algebraic-envelopes', 'Simple-F-infinity',
                'An-Artin-group-with-no', 'A-universal-group-of-type']
    selected = load(S + '/selected-domain.json')
    wanted = [d for d in domain if any(d['path'].split('/')[1].startswith(f) for f in families)]
    require(len(selected) == len(wanted) == 106, 'selected scope count')
    require({d['path'] for d in selected} == {d['path'] for d in wanted}, 'selected families')
    selected_pdf = 0
    for d in selected:
        require(d == bypath[d['path']], 'selected source mismatch')
        if d['kind'] == 'outside_pdf':
            extract(outside_map[d['path']]['local'], d['local'])
            selected_pdf += 1

    responses = lines(S + '/primary/responses.jsonl') + lines(S + '/primary/responses-more.jsonl')
    require(len(responses) == 8 and len({d['local'] for d in responses}) == 8, 'primary response scope')
    primary_pdf = 0
    for d in responses:
        require(d['status'] == 200 and d['url'].startswith('https://') and d['final_url'].startswith('https://'),
                'primary response status')
        require(d['headers'] and d['captured'], 'missing primary response metadata')
        b = checkhash(d['local'], d['sha256'])
        require(len(b) == d['bytes'], 'primary byte count')
        if 'text' in d:
            primary_pdf += 1
            checkhash(d['text'], d['text_sha256'])
            extract(d['local'], d['text'])
    require(primary_pdf == 5, 'primary PDF count')
    for name, version in [('lcm', '0907.3681v2'), ('vcs-growth', '1402.6974v2'), ('ikn', '1210.5829v1')]:
        require(version in raw(S + '/primary/' + name + '.txt').decode(), 'PDF version: ' + name)
        require(version in raw(S + '/primary/' + name + '-version.html').decode(), 'version page: ' + name)
    require('September 18, 2021' in raw(S + '/primary/lcm.txt').decode(), 'LCM retained date')
    require('September 15, 2021' in raw(S + '/primary/vcs-growth.txt').decode(), 'VCS retained date')

    passages = load(S + '/passages.json')
    require(len(passages) == 33 and len({d['label'] for d in passages}) == 33, 'passage scope')
    for d in passages:
        b = checkhash(d['local'], d['source_sha256'])
        source_lines = b.decode().splitlines(keepends=True)
        require(1 <= d['start'] <= d['end'] <= len(source_lines), 'passage range: ' + d['label'])
        text = ''.join(source_lines[d['start']-1:d['end']])
        require(text == d['text'] and sha(text.encode()) == d['sha256'], 'passage body: ' + d['label'])
        if 'path' in d:
            require(bypath[d['path']]['local'] == d['local'], 'passage provenance')

    diagnostics = subprocess.check_output([sys.executable, '-B', str(path(E + '/checks.py'))],
                                        cwd=R, env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
    require(json.loads(diagnostics) == load(E + '/checks-output.json'), 'diagnostics replay')
    # Recheck own domain and hashes after all subprocesses: no unnoticed output.
    require(inventory() == owned, 'verification changed owned domain')
    if not args.preseal:
        for name, rec in files.items():
            checkhash(name, rec['sha256'])
    print(json.dumps({
        'status': 'PASS_PRESEAL_EVIDENCE_ONLY' if args.preseal else 'PASS_EVIDENCE_ONLY',
        'mode': 'OFFLINE_READ_ONLY', 'pin': PIN, 'owned_files': len(owned),
        'tree_entries': 13223, 'manuscripts': 749, 'original_blobs_verified': 10373,
        'corpus_originals': 9340, 'outside_originals': 1033, 'outside_pdf_hashes': n_pdf,
        'search_hits': {q['name']: len(h) for q, h in zip(queries, hits)},
        'selected_representatives': len(selected), 'selected_pdf_replays': selected_pdf,
        'primary_responses': len(responses), 'primary_pdf_replays': primary_pdf,
        'passages': len(passages), 'immutable_references': len(references),
        'allowed_live_ledger_drift': drift, 'diagnostics': json.loads(diagnostics)['status'],
        'original_proof': 'NOT_INDEPENDENTLY_REVIEWED',
        'contribution': 'AUTHOR_TECHNICAL_NO_SUBSTANTIAL_NOMINATION',
        'finding_count_change': 0,
    }, sort_keys=True, indent=2))


if __name__ == '__main__':
    try:
        main()
    except Exception as exc:
        print(json.dumps({'status': 'FAIL_EVIDENCE', 'error': str(exc)}, sort_keys=True))
        raise SystemExit(1)
