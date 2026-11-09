"""Finalize hash-bound dual checks, per-case coverage, and compact evidence."""
import sys
sys.dont_write_bytecode = True
import collections
import hashlib
import json
import math
import pathlib

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent.parent


def read(p):
    return json.loads(p.read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    summary = read(HERE / 'summary.json')
    assignment = read(HERE / 'assignment.json')
    for name, rec in assignment['configurations'].items():
        key = str(rec['S_low']) + '|' + ','.join(map(str, sorted(rec['far'])))
        assert rec['key'] == key and name == '111132:' + key
        assert rec['target'] == 111132 and 0 <= rec['S_low'] < 1000
        low = [(rec['S_low'] // 10**i) % 10 + 1 for i in range(3)]
        assert all(1 <= d <= 9 for d in low)
        assert all(c % 9 == 0 and 9 <= c <= 72 for c in rec['far'])
        assert math.prod(low + [c // 9 + 1 for c in rec['far']]) == 111132
    ledger = read(HERE / 'standalone_checks.json')
    orderings = read(HERE / 'ordering_audit.json')
    kills = read(HERE / 'kill_usage.json')
    paths = {str(p) for p in (HERE / 'certs').rglob('*.jsonl')}
    assert paths == set(ledger['files']) == set(kills)
    assert set(summary['configurations']) == set(assignment['configurations']) == set(orderings['configurations'])
    domains = set()
    for file, record in ledger['files'].items():
        assert sha(pathlib.Path(file)) == record['sha256']
        assert record['result'] == record['check']['result'] == record['independent']['result'] == 'PASS'
        assert sorted(record['check']['solutions']) == sorted(record['independent']['claimed'])
        with pathlib.Path(file).open() as f:
            m = json.loads(next(f))
        domain = (m['K'], tuple(map(tuple, m['groups'])), m['qmin'])
        assert domain not in domains, ('duplicate domain', domain)
        domains.add(domain)
    assert ledger['direct_checker_sha256'] == sha(HERE.parent / 'sym/check_sym.py')
    assert ledger['independent_checker_sha256'] == sha(HERE.parent.parent / 'indep4/check_sym_F.py')
    copied = ('gen_sym.py', 'gen_precomputed.py', 'check_sym.py', 'audit_coverage.py', 'coverage_distinct.py', 'audit_orderings.py')
    assert all(sha(HERE / f) == sha(HERE.parent / 'sym2' / f) for f in copied)
    assert sha(HERE / 'check_sym.py') == sha(HERE.parent / 'sym/check_sym.py')
    for file, digest in assignment['source_hashes'].items():
        assert sha(ROOT / file) == digest
    counts = {}
    for k in range(5, 9):
        rows = [r for r in summary['configurations'].values() if r['k'] == k]
        counts[str(k)] = dict(assigned=len(rows), closed=sum(r['status'] == 'CLOSED' for r in rows),
                              open=sum(r['status'] != 'CLOSED' for r in rows))
    for name, r in summary['configurations'].items():
        assert r['distinct_coefficient_orderings'] == orderings['configurations'][name]['distinct_orderings']
    stages = {}
    attempts = collections.Counter()
    for p in sorted(HERE.glob('search_*.json')):
        data = read(p)
        attempts.update(data.keys())
        stages[p.name] = dict(configurations=len(data), statuses=dict(collections.Counter(r['status'] for r in data.values())),
                             worker_seconds=round(sum(r['seconds'] for r in data.values()), 3))
    assert set(attempts) == set(assignment['configurations'])
    final_stage = read(HERE / 'search_supplyD180.json')
    final_input = read(HERE / 'input_supplyD180.json')
    assert final_input['seconds_per_configuration'] >= 180
    assert set(final_stage) == set(final_input['keys'])
    assert all(name in final_stage for name in summary['open'])
    summary.update(counts_by_k=counts, stages=stages,
                   dual_checker_counts={'sym':dict(collections.Counter(r['check']['result'] for r in ledger['files'].values())),
                                        'F':dict(collections.Counter(r['independent']['result'] for r in ledger['files'].values()))},
                   retained_certificates=len(paths), certificate_bytes=sum(pathlib.Path(p).stat().st_size for p in paths),
                   ordering_audit=dict(result='PASS', configurations=len(orderings['configurations']),
                                       distinct_orderings=orderings['total_distinct_orderings']),
                   coverage_counts=dict(collections.Counter('COVERED' if r['status'] == 'CLOSED' else 'INCOMPLETE' for r in summary['configurations'].values())),
                   duplicate_domains=0, all_configurations_attempted=True,
                   all_still_open_configurations_escalated=True,
                   assignment_field_and_target_checks={'result':'PASS', 'configurations':len(assignment['configurations'])},
                   supply_hashes={p.name:sha(p) for p in (HERE.parent/'supply_B.json', HERE.parent/'supply_D.json')})
    (HERE / 'summary.json').write_text(json.dumps(summary, indent=1) + '\n')
    (HERE / 'coverage_audit.json').write_text(json.dumps(dict(
        configurations=summary['configurations'], counts=summary['coverage_counts'],
        finite_exception_scan=summary['finite_exception_scan'], ordering_audit=summary['ordering_audit']), indent=1) + '\n')
    note = ROOT / 'notes/highdim_sym3.md'
    text = note.read_text().split('## Final executed results')[0]
    text = text.replace('Search and validation are in progress. Final counts and evidence will be\nappended after the bounded stages and direct checker replays.\n', '')
    lines = ['## Final executed results', '', '**COMPUTED:** Newly closed/open counts for this assignment:', '']
    for k, r in counts.items():
        lines.append(f'- k={k}: {r["closed"]} closed, {r["open"]} open, {r["assigned"]} assigned.')
    lines += ['', f'Both direct checkers PASS on all {len(paths)} retained certificates, with brute L<=11. '
              'Their complete solution lists agree. No checker failure or timeout is counted as a closure.', '',
              '**PROVED (checked):** Every counted closure has a full slice cover built only from '
              'hash-bound certificates accepted by both direct checkers, together with the finite '
              'short-length scan and the complete filtered size-leaf solution lists.', '',
              f'Coverage: {len(summary["closed"])} complete configurations; {len(summary["open"])} incomplete. '
              'Every case has its coverage result, failed-cover diagnostics if open, and distinct ordering count in '
              '`coverage_audit.json`. Closed cases include the exact certificate list, coverage method, finite bound, '
              'and filtered members. No open case is claimed covered.', '',
              f'The ordering audit passes all 210 configurations and {orderings["total_distinct_orderings"]} words. '
              f'The finite exception scan checks {summary["finite_exception_scan"]["smooth_points"]} smooth integers '
              f'through {summary["finite_exception_scan"]["Lmax"]} digits and finds '
              f'{len(summary["finite_exception_scan"]["members"])} members in closed cases.', '',
              f'Certificates occupy {summary["certificate_bytes"]} bytes, with zero duplicate domains. '
              'No legacy certificates were copied.', '',
              'The first launch of precomputed24 briefly overlapped broad8 and was stopped immediately, '
              'before it produced a checkpoint or retained certificate. This transient exceeded the intended '
              '12-worker cap; later search/check pools ran sequentially with at most 12 workers. '
              'The interrupted launch log is retained separately.', '', 'Checkpointed stages:', '']
    lines += ['The supply-B 180-second pass was intentionally stopped at its saved checkpoint '
              'after the target-specific notes identified the need for the larger prime supply. '
              'The final supplyD180 pass uses the existing supply_D.json as an untrusted search aid. '
              'Primality, decimal orders and every kill are still independently recomputed by both '
              'direct checkers. Completed files from the interrupted pass are retained and checked; '
              'unsaved partial trees are discarded. The pre-supply driver is frozen in inputs/.', '']
    for stage, r in stages.items():
        lines.append(f'- `{stage}`: {r["configurations"]} configurations, {r["statuses"]}, {r["worker_seconds"]} worker seconds.')
    lines += ['', 'Evidence:', '', '- `assignment.json`: source hash and exact 210-case assignment.',
              '- `summary.json`: closed/open keys, counts, members, stages and full per-case coverage.',
              '- `standalone_checks.json` and `check_journal.jsonl`: exact direct commands, certificate hashes, both checker results.',
              '- `coverage_audit.json` and `ordering_audit.json`: slice/short-length and ordering coverage.',
              '- `kill_usage.json`: per-certificate kill dependencies, stored reference counts, exact prime orders and F-checker actual kill classifications.',
              '- `certs/`: compact nd-sym JSONL proof trees; `input_*.json` and `search_*.json`: budgets and checkpoints.',
              '- `manifest.json`: SHA-256 evidence manifest.', '',
              'Reproduction (repository root; each bounded command below 30 minutes):', '', '```sh',
              "timeout 1500 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym3/continue_sym3.py check --workers 12'",
              "timeout 1500 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym3/continue_sym3.py audit'",
              "bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym3/audit_orderings.py'",
              "bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym3/finalize_sym3.py'", '```', '']
    lines[-2:-2] = ["bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym3/verify_manifest.py'"]
    note.write_text(text + '\n'.join(lines))
    manifest = {str(p.relative_to(HERE)):sha(p) for p in sorted(HERE.rglob('*'))
                if p.is_file() and p.name != 'manifest.json' and p.suffix not in ('.log', '.tmp')}
    manifest['../../../notes/highdim_sym3.md'] = sha(note)
    (HERE / 'manifest.json').write_text(json.dumps(dict(sha256=manifest), indent=1) + '\n')
    print(json.dumps(dict(counts_by_k=counts, dual_checker_counts=summary['dual_checker_counts'],
                         coverage=summary['coverage_counts'], certificates=len(paths), bytes=summary['certificate_bytes'])))


if __name__ == '__main__':
    main()
