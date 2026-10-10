#!/usr/bin/env python3
"""Offline, READ-ONLY replay. No writes/downloads/subprocesses/bytecode/repair/reseal.

--preseal validates before the single final seal exists. Normal mode checks it.
Evidence replay and finite diagnostics are not a proof or contribution certificate.
"""
import sys
sys.dont_write_bytecode = True
import os


def guard(event, args):
    if event == 'open':
        _, mode, flags = args
        if ((mode and any(x in mode for x in 'wax+')) or
                flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND)):
            raise RuntimeError('Read-only verifier rejected write open')
    if event.startswith(('socket.', 'subprocess.')):
        raise RuntimeError('Offline verifier rejected network/subprocess: ' + event)
    if event in {'os.remove', 'os.unlink', 'os.rename', 'os.rmdir', 'os.mkdir',
                 'os.chmod', 'os.chown', 'os.truncate', 'os.symlink', 'os.link',
                 'os.utime', 'os.system', 'os.exec', 'os.posix_spawn'}:
        raise RuntimeError('Read-only verifier rejected mutation: ' + event)


sys.addaudithook(guard)
import json
import re
import hashlib
import runpy
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
BASE = Path('frontier/sources/i107_rational_tail_attachment')
EXP = Path('frontier/experiments/i107_rational_tail_attachment')
OLD = Path('frontier/sources/i105_chromatic_homotopy_discovery')
REPORT = Path('frontier/iterations/i107-rational-tail-attachment.md')
SEAL = BASE/'seal.json'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
DRIFT = {'README.md', 'frontier/README.md', 'frontier/TEN-FINDINGS.md',
         'frontier/iterations/README.md'}


def need(ok, message):
    if not ok:
        raise AssertionError(message)


def read(path):
    return (ROOT/path).read_bytes()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def js(path):
    return json.loads(read(path))


def inventory():
    files, dirs = {str(REPORT)}, set()
    for base in (BASE, EXP):
        dirs.add(str(base))
        for p in (ROOT/base).rglob('*'):
            need(not p.is_symlink(), 'Owned symlink: ' + str(p))
            rel = str(p.relative_to(ROOT))
            (files if p.is_file() else dirs).add(rel)
    return files, dirs


def check_ref(path, expected):
    need(not any(token in str(path) for token in ('i104_', 'i106_', 'i104-', 'i106-')),
         'Bound active reference: ' + str(path))
    need(sha(read(path)) == expected, 'Immutable reference SHA256: ' + str(path))


def main():
    need(sys.argv[1:] in ([], ['--preseal']), 'Only optional flag: --preseal')
    preseal = bool(sys.argv[1:])
    files, dirs = inventory()
    if preseal:
        need(not (ROOT/SEAL).exists(), 'Preseal requires absent seal')
    else:
        seal = js(SEAL)
        need(seal['pin'] == PIN, 'Seal pin')
        need(files == set(seal['owned_files']) | {str(SEAL)}, 'Exact owned file inventory')
        need(dirs == set(seal['owned_directories']), 'Exact owned directory inventory')
        need(set(seal['driftable_live']) == DRIFT, 'Only four live ledgers may drift')
        for p, h in seal['owned_files'].items():
            need(sha(read(p)) == h, 'Owned SHA256: ' + p)

    drift = []
    refs = js(BASE/'input-references.json')
    need(len(refs) == 12, 'Frozen input inventory')
    for ref in refs:
        check_ref(ref['frozen'], ref['sha256'])
        if sha(read(ref['live'])) != ref['sha256']:
            need(ref['live'] in DRIFT, 'Immutable live input changed: ' + ref['live'])
            drift.append(ref['live'])
    for name, iteration in [('original-brief.txt', '105-chromatic-homotopy-discovery'),
                            ('full-i107-brief.txt', '107-rational-tail-attachment')]:
        task = js(BASE/('inputs/frontier/iterations/iteration' + iteration + '-task.json'))
        need(read(BASE/'inputs'/name) == task['brief'].encode('utf-8'),
             'Exact extracted brief bytes: ' + name)
    need(sha(read(BASE/'inputs/frontier/iterations/i105-chromatic-homotopy-discovery.md')) ==
         'b8835a61161ea08e7e7d1a34ec084792d5ba40595d948b080bd74a94cf49e1ae',
         'Original report identity')
    parent = js(BASE/'inputs/frontier/experiments/i105-parent-verification.json')
    need(parent['seal_sha256'] == '02b2f28d604580dd91060957cd97589a8d08e8508570db9ea545b25055c9bfd1',
         'Finalized parent evidence identity')
    for ref in js(BASE/'inherited-references.json'):
        check_ref(ref['path'], ref['sha256'])
    need(js(BASE/'inputs/sources/upstream.json')['commit'] == PIN, 'Pinned revision')
    tree = js(BASE/'inputs/sources/preprints-tree.json')
    need(not tree['truncated'] and len(tree['tree']) == 13223, 'Frozen complete tree')
    blobs = {x['path']: x for x in tree['tree'] if x['type'] == 'blob'}
    domain = js(OLD/'search-domain.json')
    need(len(domain) == 10373 and len({x['path'] for x in domain}) == 10373,
         'Unique full original domain')
    need(set(blobs) == {x['path'] for x in domain}, 'Exact original position coverage')
    counts = {kind: sum(x['kind'] == kind for x in domain)
              for kind in ('corpus', 'outside_bytes', 'outside_pdf')}
    need(counts == {'corpus': 9340, 'outside_bytes': 257, 'outside_pdf': 776}, 'Inherited domain kinds')
    queries = js(OLD/'queries.json') | js(BASE/'queries.json')
    patterns = {name: re.compile(pattern, re.I) for name, pattern in queries.items()}
    hits = {name: [] for name in patterns}
    bypath = {}
    for x in domain:
        original = read(x['original_local'])
        check_ref(x['original_local'], x['original_sha256'])
        blob = hashlib.sha1(b'blob ' + str(len(original)).encode() + b'\0' + original).hexdigest()
        need(blob == x['git_sha'] == blobs[x['path']]['sha'], 'Git blob identity: ' + x['path'])
        need(len(original) == blobs[x['path']]['size'], 'Original byte length: ' + x['path'])
        data = read(x['local'])
        check_ref(x['local'], x['sha256'])
        for i, line in enumerate(data.decode('utf-8', errors='replace').splitlines(), 1):
            for name, pattern in patterns.items():
                matches = [m.group(0) for m in pattern.finditer(line)]
                if matches:
                    hits[name].append({'path': x['path'], 'local': x['local'],
                                       'splitline': i, 'text': line, 'matches': matches})
        bypath[x['path']] = x
    for name, rows in hits.items():
        base = BASE if name == 'unframed' else OLD
        saved = [json.loads(line) for line in read(base/('search-' + name + '.jsonl')).decode().splitlines()]
        need(rows == saved, 'Exact lexical sequence and occurrence multiset: ' + name)
    for x in js(BASE/'source-references.json'):
        need({k: v for k, v in x.items() if k != 'url'} == bypath[x['path']], 'Source mapping')
        need(x['url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + x['path'],
             'Exact pinned source URL')
    titles = sorted({x['path'].split('/')[1] for x in tree['tree']})
    screen = js(BASE/'companion-screen.json')
    need(len(titles) == 749 and titles == screen['all_titles'], 'Complete title inventory')
    need(screen['matches'] == [t for t in titles if re.search(screen['regex'], t, re.I)],
         'Exact companion lexical screen')
    passages = js(BASE/'reading-manifest.json')
    for x in passages:
        check_ref(x['local'], x['source_sha256'])
        text = read(x['local']).decode('utf-8')
        lines = text.split('\n')
        need(len(lines) == x['LF_fields'] and len(text.splitlines()) == x['splitlines_count'],
             'Explicit LF and splitlines counts')
        need(1 <= x['LF_start'] <= x['LF_end'] <= len(lines), 'Reading range')
        part = '\n'.join(lines[x['LF_start']-1:x['LF_end']])
        need(sha(part.encode()) == x['passage_sha256'], 'Exact reading passage hash')
        need(re.findall(r'\\label\{([^}]+)\}', part) == x['labels'], 'Exact reading labels')
    gprefix = 'preprints/Filtered-chromatic-splitting-at-generic-primes-September-25-2026/build/sections/'
    gfiles = {x['local'] for x in domain if x['path'].startswith(gprefix) and x['path'].endswith('.tex')}
    complete = {x['local'] for x in passages if x['LF_start'] == 1 and x['LF_end'] == x['LF_fields']}
    need(gfiles <= complete, 'Complete strongest generic companion reading ranges')
    verdicts = js(BASE/'verdicts.json')
    need(len(verdicts['original_proofs']) == 15 and verdicts['repairs'] == [], 'Separate original verdicts')
    need(verdicts['new_theorem']['accepted_findings_after'] == 8, 'No forced nomination')
    report = read(REPORT).decode('utf-8')
    need(report.count('\\[') == report.count('\\]'), 'Balanced report display math')
    need(all(line.count('$') % 2 == 0 for line in report.splitlines()), 'Balanced inline math per line')
    need(not any(ord(c) < 32 and c not in '\n\t' for c in report), 'No escaped control characters in report')
    diagnostics = runpy.run_path(str(ROOT/EXP/'diagnostics.py'))['run']()
    print(json.dumps({'status': 'PRESEAL PASS' if preseal else 'PASS',
                      'original_positions': len(domain), 'kinds': counts,
                      'lexical_matching_lines': {k: len(v) for k, v in hits.items()},
                      'reading_passages': len(passages), 'complete_G_sections': len(gfiles),
                      'drifted_live_ledgers': sorted(drift), 'diagnostics': diagnostics,
                      'scope': 'Evidence identity and finite bookkeeping only; no proof or contribution certification.'},
                     sort_keys=True))


if __name__ == '__main__':
    main()
