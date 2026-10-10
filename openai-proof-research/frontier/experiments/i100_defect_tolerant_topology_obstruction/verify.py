#!/usr/bin/env python3
"""Offline READ-ONLY verification: no network, writes, bytecode, repair or reseal.

Children are the hash-bound unchanged I97/I94 read-only verifiers, this package's
finite diagnostic, pdftotext to stdout and pdftoppm to stdout. --preseal only
omits the final owned-inventory seal check; it never creates a seal.
"""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess

ROOT = Path(__file__).resolve().parents[3]
S = 'frontier/sources/i100_defect_tolerant_topology_obstruction'
E = 'frontier/experiments/i100_defect_tolerant_topology_obstruction'
OLD = 'frontier/sources/i97_relative_involution_stabilization'
REPORT = 'frontier/iterations/i100-defect-tolerant-topology-obstruction.md'
SEAL = S + '/seal.json'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
DRIFT = {'README.md', 'frontier/README.md', 'frontier/TEN-FINDINGS.md',
         'frontier/iterations/README.md'}


def check(test, message):
    if not test:
        raise AssertionError(message)


def raw(path):
    return (ROOT / path).read_bytes()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def doc(path):
    return json.loads(raw(path))


def command(args):
    run = subprocess.run(args, cwd=ROOT, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE,
                         env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'))
    check(run.returncode == 0, 'Child failure: ' + str(args) + '\n' +
          run.stdout.decode(errors='replace') + '\n' +
          run.stderr.decode(errors='replace'))
    return run.stdout


def owned():
    paths = [REPORT]
    for base in (S, E):
        paths.extend(str(p.relative_to(ROOT)) for p in (ROOT / base).rglob('*')
                     if p.is_file())
    return sorted(p for p in paths if p != SEAL)


def main():
    check(sys.argv[1:] in ([], ['--preseal']), 'only optional --preseal')
    pre = bool(sys.argv[1:])
    files = owned()
    check(not any('__pycache__' in p or p.endswith('.pyc') for p in files),
          'unexpected bytecode')
    if not pre:
        seal = doc(SEAL)
        check(seal['pin'] == PIN and seal['excluded_owned_files'] == [SEAL],
              'seal scope')
        check(seal['files'] == [dict(path=p, sha256=sha(raw(p))) for p in files],
              'owned inventory or hash mismatch')
    inputs = doc(S + '/inputs.json')
    check({x['original'] for x in inputs if x['may_drift']} == DRIFT,
          'drift policy')
    drift = []
    for x in inputs:
        check(sha(raw(x['snapshot'])) == x['sha256'], 'snapshot ' + x['snapshot'])
        if sha(raw(x['original'])) != x['sha256']:
            check(x['may_drift'] and x['original'] in DRIFT,
                  'immutable original ' + x['original'])
            drift.append(x['original'])
    refs = doc(S + '/immutable-references.json')
    for x in refs:
        check(not re.search(r'i9[89][_-]', x['path']), 'I98/I99 binding')
        check(sha(raw(x['path'])) == x['sha256'], 'reference ' + x['path'])
    check(sha(raw(OLD + '/seal.json')) ==
          '125cb07d18d02a7a3d82b1181be8fb08857dcc53cd2c400b142ae3a7056a8fc6',
          'original I97 seal')
    # Trust executable bytes only after the preceding immutable-reference check.
    inherited = json.loads(command([sys.executable, '-B',
        'frontier/experiments/i97_relative_involution_stabilization/verify.py']))
    check(inherited['status'] == 'PASS' and
          inherited['original_blob_positions'] == 10373 and
          inherited['inherited_pdf_hash_bindings'] == 776, 'inherited replay')
    tree = doc(S + '/snapshots/sources/preprints-tree.json')
    check(not tree['truncated'] and len(tree['tree']) == 13223, 'complete tree')
    blobs = {x['path']: x['sha'] for x in tree['tree'] if x['type'] == 'blob'}
    titles = sorted({p.split('/')[1] for p in blobs})
    check(len(blobs) == 10373 and len(titles) == 749, 'domain counts')
    domain = doc('frontier/sources/i94_topology_transformation_discovery/search-domain.json')
    check({x['path'] for x in domain} == set(blobs), 'domain bijection')
    screen = doc(S + '/selection.json')
    check(screen['all_title_hits'] == [t for t in titles if
          re.search(screen['title_pattern'], t, re.I)], 'title variants')
    selected = [x for x in domain if x['path'].split('/')[1] in
                screen['selected_families']]
    check(selected == doc(S + '/selected-inventory.json'), 'family completeness')
    patterns = {k: re.compile(v, re.I) for k, v in doc(S + '/queries.json').items()}
    hits = {k: [] for k in patterns}
    for x in domain:
        for i, line in enumerate(raw(x['local']).decode(errors='replace').splitlines(), 1):
            for k, pattern in patterns.items():
                if pattern.search(line):
                    hits[k].append(dict(path=x['path'], line=i, text=line))
    for k, rows in hits.items():
        check(rows == [json.loads(line) for line in
              raw(S + '/search-' + k + '.jsonl').decode().splitlines()],
              'search replay ' + k)
    reads = doc(S + '/read-manifest.json')
    for x in reads:
        data = raw(x['local'])
        lines = data.decode(errors='replace').splitlines()
        check(sha(data) == x['sha256'], 'source ' + x['local'])
        check(len(lines) == x['total_splitlines'] and
              data.count(b'\n') == x['total_LF_newlines'], 'line convention')
        a, z = x['start'], x['end']
        check(1 <= a <= z <= len(lines), 'read range')
        passage = ('\n'.join(lines[a-1:z]) + '\n').encode()
        check(sha(passage) == x['passage_sha256'] and
              passage == raw(x['passage_file']), 'selected passage')
    requests = doc(S + '/external/requests.json')
    for x in requests:
        check('error' not in x, 'failed PDF retrieval is not usable input')
        check(sha(raw(x['pdf'])) == x['sha256'] and
              sha(raw(x['text'])) == x['text_sha256'], 'primary bytes')
        check(sha(command(['pdftotext', '-layout', x['pdf'], '-'])) ==
              x['text_sha256'], 'PDF text replay')
    render = doc(S + '/render.json')
    check(sha(raw(render['png'])) == render['sha256'], 'render bytes')
    rendered = command(['pdftoppm', '-f', str(render['page']), '-l',
                        str(render['page']), '-scale-to', str(render['scale_to']),
                        '-png', '-singlefile', render['pdf']])
    check(sha(rendered) == render['sha256'], 'render replay to stdout')
    diagnostic = json.loads(command([sys.executable, '-B', E + '/diagnostics.py']))
    check(diagnostic == doc(E + '/diagnostic-results.json'), 'diagnostic replay')
    print(json.dumps(dict(status='PASS', mode='preseal' if pre else 'final-seal',
        owned_files=len(files), immutable_references=len(refs),
        allowed_ledger_drift=drift, manuscripts=749, original_blob_positions=10373,
        inherited_pdf_hash_bindings=776, inherited_I97_replay=inherited,
        read_records=len(reads), selected_representations=len(selected),
        new_primary_PDF_replays=len(requests), render_replays=1,
        search_counts={k: len(v) for k, v in hits.items()}, diagnostics=diagnostic,
        limits='Evidence and finite algebra only; no actual residual realization, '
               'involution, stronger stabilization bound, full-corpus semantic '
               'audit, all-PDF extraction, or independent novelty certification.'),
        indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
