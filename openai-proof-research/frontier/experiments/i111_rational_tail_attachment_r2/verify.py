#!/usr/bin/env python3
"""Offline READ-ONLY evidence replay. No writes, network, subprocesses,
bytecode, repairs or resealing. --preseal requires an absent final seal.
Mathematical proof and contribution assessment are in the review, not here.
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
BASE = Path('frontier/sources/i111_rational_tail_attachment_r2')
EXP = Path('frontier/experiments/i111_rational_tail_attachment_r2')
OLD = Path('frontier/sources/i105_chromatic_homotopy_discovery')
I107 = Path('frontier/sources/i107_rational_tail_attachment')
REPORT = Path('frontier/reviews/i111-rational-tail-attachment-r2.md')
SEAL = BASE/'seal.json'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
DRIFT = {'README.md', 'frontier/README.md', 'frontier/TEN-FINDINGS.md',
         'frontier/iterations/README.md'}


def need(ok, message):
    if not ok:
        raise AssertionError(message)


def read(p):
    return (ROOT/p).read_bytes()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def js(p):
    return json.loads(read(p))


def inventory():
    files, dirs = {str(REPORT)}, set()
    for base in (BASE, EXP):
        dirs.add(str(base))
        for p in (ROOT/base).rglob('*'):
            need(not p.is_symlink(), 'Owned symlink: ' + str(p))
            rel = str(p.relative_to(ROOT))
            (files if p.is_file() else dirs).add(rel)
    return files, dirs


def check_ref(p, h):
    need(not any(t in str(p) for t in ('i109_', 'i109-', 'i110_', 'i110-')),
         'Bound active artifact: ' + str(p))
    need(sha(read(p)) == h, 'Immutable SHA256: ' + str(p))


def main():
    need(sys.argv[1:] in ([], ['--preseal']), 'Only optional flag: --preseal')
    preseal = bool(sys.argv[1:])
    files, dirs = inventory()
    if preseal:
        need(not (ROOT/SEAL).exists(), 'Preseal requires absent seal')
    else:
        seal = js(SEAL)
        need(seal['pin'] == PIN, 'Final seal pin')
        need(files == set(seal['owned_files']) | {str(SEAL)}, 'Exact owned files')
        need(dirs == set(seal['owned_directories']), 'Exact owned directories')
        need(set(seal['driftable_live']) == DRIFT, 'Only four live ledgers may drift')
        for p, h in seal['owned_files'].items():
            need(sha(read(p)) == h, 'Owned SHA256: ' + p)
        need(js(seal['preseal_validation'])['exit_code'] == 0, 'Successful preseal validation')

    drift = []
    refs = js(BASE/'input-references.json')
    need(len(refs) == 11, 'Frozen input inventory')
    for r in refs:
        check_ref(r['frozen'], r['sha256'])
        if sha(read(r['live'])) != r['sha256']:
            need(r['live'] in DRIFT, 'Immutable live input changed: ' + r['live'])
            drift.append(r['live'])
    for name, iteration in [('full-original-i107-brief.txt', '107-rational-tail-attachment'),
                            ('full-i111-brief.txt', '111-rational-tail-attachment-r2')]:
        task = js(BASE/('inputs/frontier/iterations/iteration' + iteration + '-task.json'))
        need(read(BASE/'inputs'/name) == task['brief'].encode('utf-8'),
             'Exact full brief without appended newline: ' + name)
    need(sha(read(BASE/'inputs/frontier/iterations/i107-rational-tail-attachment.md')) ==
         'bacefb963889524db590ea47f7162537394c5c6999f2a07bc0b0526c684fe598',
         'Original I107 report identity')
    parent = js(BASE/'inputs/frontier/experiments/i107-parent-verification.json')
    need(parent['seal_sha256'] == sha(read(I107/'seal.json')) ==
         'b3ab1a47704bb979a311920bd6eb85feb7b5fdf9b7ec9498e9d76e2cf32c1adf',
         'Original finalized parent seal identity')
    immutable = js(BASE/'immutable-references.json')
    need(len({r['path'] for r in immutable}) == len(immutable), 'Unique immutable reference paths')
    for r in immutable:
        check_ref(r['path'], r['sha256'])
    need(js(BASE/'inputs/sources/upstream.json')['commit'] == PIN, 'Pinned revision')

    tree = js(I107/'inputs/sources/preprints-tree.json')
    need(not tree['truncated'] and len(tree['tree']) == 13223, 'Complete immutable tree')
    blobs = {x['path']: x for x in tree['tree'] if x['type'] == 'blob'}
    domain = js(OLD/'search-domain.json')
    need(len(domain) == len({x['path'] for x in domain}) == 10373, 'Full unique original positions')
    need(set(blobs) == {x['path'] for x in domain}, 'Exact original position coverage')
    kinds = {k: sum(x['kind'] == k for x in domain) for k in ('corpus', 'outside_bytes', 'outside_pdf')}
    need(kinds == {'corpus': 9340, 'outside_bytes': 257, 'outside_pdf': 776}, 'Domain representation kinds')
    queries = js(OLD/'queries.json') | js(I107/'queries.json')
    need(set(queries) == {'homotopy', 'bridges', 'unframed'}, 'Three exact inherited lexical expressions')
    patterns = {name: re.compile(q, re.I) for name, q in queries.items()}
    hits = {name: [] for name in patterns}
    bypath = {}
    for x in domain:
        original = read(x['original_local'])
        check_ref(x['original_local'], x['original_sha256'])
        gitsha = hashlib.sha1(b'blob ' + str(len(original)).encode() + b'\0' + original).hexdigest()
        need(gitsha == x['git_sha'] == blobs[x['path']]['sha'], 'Original Git blob identity: ' + x['path'])
        need(len(original) == blobs[x['path']]['size'], 'Original byte length: ' + x['path'])
        data = read(x['local'])
        check_ref(x['local'], x['sha256'])
        for n, line in enumerate(data.decode('utf-8', errors='replace').splitlines(), 1):
            for name, pattern in patterns.items():
                matches = [m.group(0) for m in pattern.finditer(line)]
                if matches:
                    hits[name].append({'path': x['path'], 'local': x['local'],
                                       'splitline': n, 'text': line, 'matches': matches})
        bypath[x['path']] = x
    for name, rows in hits.items():
        base = I107 if name == 'unframed' else OLD
        saved = [json.loads(s) for s in read(base/('search-' + name + '.jsonl')).decode().splitlines()]
        need(rows == saved, 'Exact ordered lexical occurrence sequence: ' + name)
    for r in js(BASE/'source-references.json'):
        need({k: v for k, v in r.items() if k != 'url'} == bypath[r['path']], 'Pinned read source mapping')
        need(r['url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + r['path'], 'Pinned URL')
    titles = sorted({x['path'].split('/')[1] for x in tree['tree']})
    screen = js(I107/'companion-screen.json')
    need(len(titles) == 749 and titles == screen['all_titles'], 'Complete title inventory')
    need(screen['matches'] == [t for t in titles if re.search(screen['regex'], t, re.I)], 'Lexical companion screen')

    passages = js(BASE/'reading-manifest.json')
    coverage = {}
    for r in passages:
        check_ref(r['local'], r['source_sha256'])
        text = read(r['local']).decode('utf-8')
        lines = text.split('\n')
        need(len(lines) == r['LF_fields'] and len(text.splitlines()) == r['splitlines_count'], 'LF/splitlines counts')
        need(1 <= r['LF_start'] <= r['LF_end'] <= len(lines), 'Passage range')
        part = '\n'.join(lines[r['LF_start']-1:r['LF_end']])
        need(sha(part.encode()) == r['passage_sha256'], 'Exact LF passage bytes')
        need(re.findall(r'\\label\{([^}]+)\}', part) == r['labels'], 'Exact passage labels')
        coverage.setdefault(r['local'], set()).update(range(r['LF_start'], r['LF_end']+1))
    complete_read = 0
    for p, lines in coverage.items():
        if p.endswith('.tex') and not p.endswith('/05-analytic.tex'):
            need(lines == set(range(1, len(read(p).decode().split('\n'))+1)), 'Complete selected proof section: ' + p)
            complete_read += 1
    verdicts = js(BASE/'verdicts.json')
    need(len(verdicts['original_proofs']) == 7 and all(x['verdict'] == 'PASS WITHOUT REPAIRS' for x in verdicts['original_proofs']), 'Separate original-proof verdicts')
    need(verdicts['repairs'] == verdicts['missing_lemmas'] == [], 'No silent repair classification')
    need(verdicts['accepted_findings_before'] == verdicts['accepted_findings_after'] == 8 and not verdicts['substantial_nomination'], 'Technical count unchanged')
    report = read(REPORT).decode('utf-8')
    need(not any(ord(c) < 32 and c not in '\n\t' for c in report), 'Report control characters')
    need('PASS WITHOUT REPAIRS' in report and 'eight accepted findings remain eight' in report.lower(), 'Review disposition')
    diagnostics = runpy.run_path(str(ROOT/EXP/'diagnostics.py'))['run']()
    print(json.dumps({'status': 'PRESEAL PASS' if preseal else 'PASS',
                      'original_positions': len(domain), 'tree_entries': len(tree['tree']),
                      'manuscripts': len(titles), 'kinds': kinds,
                      'lexical_matching_lines': {k: len(v) for k, v in hits.items()},
                      'reading_passages': len(passages), 'complete_read_sections': complete_read,
                      'immutable_references': len(immutable),
                      'drifted_live_ledgers': sorted(drift), 'diagnostics': diagnostics,
                      'scope': 'Evidence identity and finite diagnostics only; no universal-proof or contribution certification.'}, sort_keys=True))


if __name__ == '__main__':
    main()
