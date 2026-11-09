"""Hash-bound kill ledger, counted results, notes and manifest; no proof search."""
import sys
sys.dont_write_bytecode = True
import collections
import hashlib
import json
import math
import pathlib

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def load(p):
    return json.loads(pathlib.Path(p).read_text())


def digest(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def save(name,obj):
    (HERE/name).write_text(json.dumps(obj,indent=1)+'\n')


def main():
    summary = load(HERE/'summary.json')
    checks = load(HERE/'dual_checks.json')
    supply = {r[0]:r for r in load(HERE/'supply.json')}
    orders = {}
    def order10(p):
        if p in orders:
            return orders[p]
        d = supply[p][1]
        assert pow(10,d,p)==1
        factor,remaining = 2,d
        while factor*factor<=remaining:
            if remaining%factor==0:
                while remaining%factor==0:
                    remaining//=factor
                while d%factor==0 and pow(10,d//factor,p)==1:
                    d//=factor
            factor += 1
        if remaining>1:
            while d%remaining==0 and pow(10,d//remaining,p)==1:
                d//=remaining
        orders[p] = d
        return d
    usage = {}
    for file, records in checks['files'].items():
        assert set(records)=={'M','F'}
        assert all(r['result']=='PASS' for r in records.values()), (file,records)
        p = pathlib.Path(file)
        assert all(r['sha256']==digest(p) for r in records.values())
        with p.open() as stream:
            meta = json.loads(next(stream))
            refs, primes, size_solutions, nodes = collections.Counter(),set(),0,0
            for line in stream:
                n = json.loads(line)
                nodes += 1
                if n['k']=='i':
                    M,ps = n['m2'],n['rest']
                elif 'prime' in n['x']:
                    M,ps = n['m'],[n['x']['prime']]
                else:
                    refs['exact_size_leaf'] += 1
                    size_solutions += len(n['x']['sol'])
                    ps = []
                for prime in ps:
                    primes.add(prime)
                    refs['aligned_prime_reference' if M%order10(prime)==0 else 'unaligned_sumset_reference'] += 1
        deps = []
        if primes:
            deps.append('prime_coset')
            if refs['unaligned_sumset_reference']:
                deps.append('unaligned_sumset')
            if meta.get('pin_digits'):
                deps.append('decimal_tail_coset_k%d'%meta['pin_digits'])
            if meta.get('pin2'):
                deps.append('mod8_parity')
        if refs['exact_size_leaf']:
            deps.append('exact_size')
        usage[file] = {'sha256':digest(p),'bytes':p.stat().st_size,'nodes':nodes,
                       'meta':meta,'dependencies':deps,'reference_counts':dict(refs),
                       'prime_orders':{str(prime):order10(prime) for prime in sorted(primes)},
                       'declared_size_solutions':size_solutions,'dual_results':{w:r['result'] for w,r in records.items()},
                       'new':HERE in p.parents}
    save('kill_usage.json',usage)
    assignment = load(HERE/'assignment.json')['configurations']
    stages,attempted = {},collections.Counter()
    for p in sorted(HERE.glob('search_*.json')):
        rows = load(p)
        attempted.update(rows.keys())
        stages[p.name] = {'attempts':len(rows),'statuses':dict(collections.Counter(r['status'] for r in rows.values())),
                          'worker_seconds':round(sum(r['seconds'] for r in rows.values()),3),
                          'partial_lifts':sum(r.get('partial',{}).get('lifts',0) for r in rows.values()),
                          'reasons':dict(collections.Counter(r.get('reason',r['status']) for r in rows.values()))}
    assert set(attempted)==set(assignment), 'unattempted assignment'
    assert all(attempted[k]>=2 for k in summary['open']), 'open case lacks second schedule'
    assert set(map(str,(HERE/'certs').rglob('*.jsonl'))) <= set(checks['files'])
    used = {p for r in summary['configurations'].values() if r['status']=='CLOSED' for p in r['domains']}
    for row in summary['configurations'].values():
        if row['status']=='CLOSED':
            row['kill_dependencies']=sorted({d for p in row['domains'] for d in usage[p]['dependencies']})
    summary.update(stages=stages,all_assigned_attempted=True,all_open_escalated=True,
                   dual_check_counts=checks['counts'],
                   new_certificates=sum(r['new'] for r in usage.values()),
                   reused_certificates=sum(not r['new'] for r in usage.values()),
                   new_certificate_bytes=sum(r['bytes'] for r in usage.values() if r['new']),
                   largest_new_certificate_bytes=max(r['bytes'] for r in usage.values() if r['new']),
                   closure_certificates=len(used),
                   kill_dependencies=dict(collections.Counter(d for r in usage.values() for d in r['dependencies'])),
                   closure_kill_dependencies=dict(collections.Counter(d for p in used for d in usage[p]['dependencies'])),
                   checker_hashes=checks['checker_hashes'],
                   hybrid_tests=load(HERE/'hybrid_test_results.json'),
                   ablation=load(HERE/'ablation_results.json'),
                   ordering_audit={k:v for k,v in load(HERE/'ordering_audit.json').items() if k!='configurations'})
    added_primes = {r[0] for r in load(HERE/'prime_search.json')['new']}
    summary['added_prime_witnesses'] = sorted({int(p) for r in usage.values() for p in r['prime_orders'] if int(p) in added_primes})
    prime_audit = load(HERE/'prime_supply_audit.json')
    assert prime_audit['result']=='PASS' and prime_audit['primes']==len(added_primes)
    summary['prime_supply_audit'] = {k:v for k,v in prime_audit.items() if k!='results'}
    save('summary.json',summary)
    note = ROOT/'notes/highdim_sym4.md'
    text = note.read_text().split('\n## Executed results\n')[0]
    lines = ['', '## Executed results', '',
             '**COMPUTED; closures PROVED (dual-checked cover).** Counts below use dimension k=1+far digits, matching the sym2 count convention.', '']
    for target,dims in summary['counts_by_target_dimension'].items():
        for dim,row in dims.items():
            lines.append(f'- Target {target}, k={dim}: {row["closed"]} closed, {row["open"]} open, {row["assigned"]} assigned.')
    lines += ['', 'Exact newly closed keys:', '', '```text', *summary['closed'], '```', '',
              f'Direct original-checker results: {checks["counts"]}. All {len(usage)} retained/reused certificates were invoked as original CLI entrypoints, without importing or patching either checker. The replay orchestrator only schedules subprocesses. Both use a brute box through L=10; declared solution lists agree.', '',
              f'Certificates: {summary["new_certificates"]} new ({summary["new_certificate_bytes"]} bytes total; largest {summary["largest_new_certificate_bytes"]} bytes), {summary["reused_certificates"]} reused sym2 pieces, {len(used)} certificates used by complete new covers. Reused pieces remain in their original locations and were replayed anew.', '',
              f'Coverage: {summary["coverage_counts"]}. Every closure passes the independently replayed unordered/v2 slice cover; open configurations retain explicit missing-domain reasons. The baseline v2 inventory contains {summary["v2_terminal_obligations"]} terminal obligations across all 134 keys. All {summary["ordering_audit"]["total_distinct_orderings"]} distinct coefficient orderings pass the inverse-group bijection audit. Inventory completeness is not a closure claim for the open configurations.', '',
              f'Finite exception scan: {summary["finite_exception_scan"]}. All declared size solutions are also filtered back to the original decimal configuration and target in the coverage auditor.', '',
              f'Hybrid comparison: {summary["hybrid_tests"]}. The independent small-box slice tests additionally pass 72 labelled cases (780 points) and 72 position-partition cases (585 canonical points).', '',
              'Search stages:', '']
    for stage,row in stages.items():
        lines.append(f'- `{stage}`: {row["attempts"]} attempts; {row["statuses"]}; {row["worker_seconds"]} worker seconds; reasons {row["reasons"]}.')
    prime = load(HERE/'prime_search.json')
    lines += ['', f'Prime search: all d=1..{prime["max_d"]} attempted; {len(prime["new"])} added primes, {len(supply)} total supply entries. A separate trial-division and exact-order audit accepts all {prime_audit["primes"]} new entries (`prime_supply_audit.json`). `prime_search.json` reports unsplit or large probable cofactors; no complete factorization claim is made. `prime_ranking.json` records decimal orders and subgroup indices. Added-prime witnesses actually present in retained certificates: {summary["added_prime_witnesses"]}. The targeted period-50 pass yielded no complete cover; no closure gain is attributed to the larger supply.', '',
              'Ablation on the two first-pass successes (same 25-second bound, <=8 workers):', '']
    for row in summary['ablation']:
        lines.append(f'- `{row["key"]}` / {row["variant"]}: {row["status"]}, {row["seconds"]} s, {row["lifts"]} lifts, {row["nodes"]} nodes.')
    lines += ['', 'All complete ablation certificates are retained and dual-checked too. These two selected cases test attribution of the observed successes; they are not an unbiased performance benchmark.', '',
              f'Kill-type dependency ledger: {summary["kill_dependencies"]}; closure-only dependencies: {summary["closure_kill_dependencies"]}. Reference counts distinguish aligned prime tests, unaligned sumsets and exact-size leaves; decimal-tail/mod8 dependencies are conservatively recorded whenever enabled. No kill type beyond Agent F\'s audited types is used.', '',
              'Needed checker extension remains pin_digits>3 up to qmin. It was not used. Other open-case budget or modulus failures are search limitations, with full traces in stage JSON files; they imply no impossibility theorem.', '',
              '## Reproduction', '', '```sh',
              "timeout 600 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym4/continue_sym2.py search --stage tailrank235 --seconds 20 --workers 12 --schedule 2,3,2,3,5,2 --precompute --modulus-digits 72 --depth 250'",
              "timeout 900 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym4/continue_sym2.py search --stage floor235 --seconds 30 --workers 12 --schedule 2,3,5,2,3,2,7 --extra-floor 2 --position-slices --precompute --modulus-digits 72 --depth 250'",
              "timeout 180 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym4/continue_sym2.py search --stage period50 --seconds 15 --workers 12 --schedule 2,5,5,3,2,3,7 --selection period50_selection.json --precompute --modulus-digits 72 --depth 250'",
              "timeout 1500 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym4/replay_dual.py --workers 12'",
              "timeout 300 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym4/audit_coverage.py'",
              "bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym/check_sym.py verification/highdim/sym4/certs/tailrank235/K2366_q3_c9_9_45_54.jsonl 10'",
              "bash -c 'ulimit -v 8000000; python3 -I verification/indep4/check_sym_F.py verification/highdim/sym4/certs/tailrank235/K2366_q3_c9_9_45_54.jsonl 10 --json'",
              "bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym4/finalize.py'",
              "bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym4/verify_manifest.py'", '```', '',
              'The exact driver loaded at the start of the first two searches is preserved in `source_snapshots/continue_sym2_initial.py`; its hash matches both input ledgers. Later driver edits corrected the reconcile/check/audit entrypoints for sym4 and did not change the search path. `prepare_evidence.py` verifies this snapshot and the assignment source hash.', '',
              'Main files: `summary.json`, `coverage_audit.json`, `v2_obligations.json`, `ordering_audit.json`, `dual_checks.json`, `dual_journal.jsonl`, `kill_usage.json`, `prime_search.json`, `prime_ranking.json`, `hybrid_test_results.json`, `ablation_results.json`, `input_*.json`, `search_*.json`, and `certs/`. All are under `verification/highdim/sym4/`. The manifest binds these and this note; logs are excluded.', '']
    note.write_text(text+'\n'.join(lines))
    manifest = {str(p.relative_to(HERE)):digest(p) for p in sorted(HERE.rglob('*'))
                if p.is_file() and p.name!='manifest.json' and p.suffix not in ('.log','.tmp') and '__pycache__' not in p.parts}
    manifest['../../../notes/highdim_sym4.md'] = digest(note)
    save('manifest.json',{'sha256':manifest,'excludes':['*.log','*.tmp','__pycache__']})
    print(json.dumps({'counts':summary['counts_by_target_dimension'],'checkers':checks['counts'],
                      'new_bytes':summary['new_certificate_bytes'],'manifest_files':len(manifest)}))


if __name__=='__main__':
    main()
