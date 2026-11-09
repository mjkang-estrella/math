"""Write the exact assignment, executed results, and hash manifest."""
import sys
sys.dont_write_bytecode = True
import collections
import hashlib
import json
import math
import pathlib

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent.parent


def load(p):
    return json.loads(p.read_text())


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    assignment = load(HERE / 'assignment.json')
    for name, rec in assignment['configurations'].items():
        key = str(rec['S_low']) + '|' + ','.join(map(str, sorted(rec['far'])))
        assert rec['key'] == key and name == str(rec['target']) + ':' + key
        low = [(rec['S_low'] // 10**i) % 10 + 1 for i in range(3)]
        assert all(1 <= d <= 9 for d in low) and 0 <= rec['S_low'] < 1000
        assert all(c % 9 == 0 and 9 <= c <= 72 for c in rec['far'])
        assert math.prod(low + [c // 9 + 1 for c in rec['far']]) == rec['target']
    summary = load(HERE / 'summary.json')
    checks = load(HERE / 'standalone_checks.json')
    assert checks['checker_sha256'] == digest(HERE / 'check_sym.py')
    assert digest(HERE / 'check_sym.py') == digest(HERE / 'inputs/check_sym.original.py')
    assert digest(HERE / 'gen_sym.py') == digest(HERE / 'inputs/gen_sym.original.py')
    for file, expected in assignment['source_hashes'].items():
        assert digest(ROOT / file) == expected, ('source assignment changed', file)
    assert all(r['result'] == 'PASS' for r in checks['files'].values())
    orderings = load(HERE / 'ordering_audit.json')
    assert orderings['result'] == 'PASS' and set(orderings['configurations']) == set(assignment['configurations'])
    for k in summary['closed']:
        assert summary['configurations'][k]['distinct_coefficient_orderings'] == orderings['configurations'][k]['distinct_orderings']
    summary['ordering_audit'] = {'result': 'PASS', 'configurations': len(orderings['configurations']),
                                 'total_distinct_orderings': orderings['total_distinct_orderings']}
    summary['assignment_field_and_target_checks'] = {'result': 'PASS', 'configurations': len(assignment['configurations'])}
    cover_tests = load(HERE / 'distinct_cover_tests.json')
    assert cover_tests['result'] == 'PASS'
    assert cover_tests['position_partition']['result'] == 'PASS'
    summary['coverage_methods'] = dict(collections.Counter(c['coverage_method'] for c in summary['configurations'].values() if c['status'] == 'CLOSED'))
    auditor = load(HERE / 'inputs/indep4/summary_F.json')
    summary['independent_auditor_prior_sym_results'] = {'certificates': auditor['certs'], 'results': auditor['results'],
                                                      'scope': 'prior 121 sym closures; kill-type proofs, not a replay of sym2 certificates'}
    label_tests = load(HERE / 'kill_label_tests.json')
    assert label_tests['result'] == 'PASS'
    summary['kill_label_tests'] = label_tests
    cache_test = load(HERE / 'cache_test_results.json')
    assert cache_test['result'] == 'PASS'
    summary['cache_inheritance_test'] = {k: cache_test[k] for k in ('result', 'context', 'inherited_domains')}
    stages = {}
    attempted = collections.Counter()
    for p in sorted(HERE.glob('search_*.json')):
        data = load(p)
        stages[p.name] = {'configurations': len(data), 'statuses': dict(collections.Counter(r['status'] for r in data.values())),
                          'worker_seconds': round(sum(r['seconds'] for r in data.values()), 3),
                          'partial_lifts': sum(r.get('partial', {}).get('lifts', 0) for r in data.values()),
                          'completed_lifts': sum(j.get('lifts', 0) for r in data.values() for j in r.get('jobs', []))}
        attempted.update(data.keys())
    assert set(attempted) == set(assignment['configurations']), 'unattempted assignment'
    assert all(attempted[k] >= 2 for k in summary['open']), 'an open case lacks escalation'
    own = set(str(p) for p in (HERE / 'certs').rglob('*.jsonl'))
    control = set(str(p) for p in (HERE / 'controls').glob('*.jsonl')) | set(str(p) for p in HERE.glob('smoke.jsonl'))
    assert own | control <= set(checks['files']), 'unreplayed generated certificate'
    summary['stages'] = stages
    summary['all_configurations_attempted'] = True
    summary['all_still_open_configurations_escalated'] = True
    summary['new_certificates'] = len(own)
    summary['inherited_certificates_replayed'] = len(checks['files']) - len(own | control)
    summary['control_certificates_replayed'] = len(control)
    used = {p for c in summary['configurations'].values() if c['status'] == 'CLOSED' for p in c['domains']}
    usage = load(HERE / 'kill_usage.json')
    summary['closure_certificate_count'] = len(used)
    summary['closure_dependency_counts'] = dict(collections.Counter(d for p in used for d in usage[p]['dependencies']))
    refs = collections.Counter()
    for p in used:
        refs.update(usage[p]['reference_counts'])
    summary['closure_reference_counts'] = dict(refs)
    (HERE / 'summary.json').write_text(json.dumps(summary, indent=1) + '\n')
    lines = ['# Sym2: remaining high-dimensional persistence configurations', '',
             '**COMPUTED** labels executed finite searches and counts. **PROVED (checked)** labels complete certificate and slice-cover replays. BUDGET is still open; these computations do not settle multiplicative persistence.', '',
             '## Exact assignment after codex, codex3a, codex3b and sym', '',
             f'The `codex/results_t14112.json` universe contains {assignment["baseline_count"]} configurations. The union of its CLOSED records, codex3a CLOSED, codex3b CLOSED and sym closed keys has {assignment["previously_closed"]} keys. The exact complement has {assignment["open_14112_count"]} keys. Source snapshots and SHA-256 hashes are in `sym2/inputs/` and `assignment.json`.', '',
             'The 210 cases in dimensions 6–8 match `sym/summary.json` BUDGET exactly. The complement additionally contains 8 dimension-4, 311 dimension-5 and 2 dimension-9 cases. The dimension-9 cases are included rather than silently excluded. The last open target-32 configuration is `11|9,9,9` (dimension 4, K=98, initial qmin=3).', '']
    for dim, keys in assignment['open_by_dimension'].items():
        lines += [f'### Target 14112, dimension {dim}: {len(keys)} assigned', '', '```text', *keys, '```', '']
    lines += ['## Search and proof procedure', '',
              'For an original key, K=9*S_low-1 and X=10^L+K+sum(c*10^q)=9*n. The far positions are pairwise distinct and satisfy 3<=q<L. Fixing a low position adds c*10^q to K. A terminal certificate has all remaining positions, and L, above its qmin floor, which guarantees v2(X)=v2(K). Raising that floor to at least v2(K)+3 makes the mod-8 exponent pin valid; the split low branches and short-length scan supply the complete original cover.', '',
              'The required generator, checker, coverage auditor and supporting scripts were copied from sym into sym2. `gen_sym.py` and `check_sym.py` are byte-identical to those copied sources. All writes stay under `verification/highdim/sym2/` and this note; no git commit was made. All Python entrypoints use isolated stdlib Python under `ulimit -v 8000000`. Search/check commands are timeout-bounded below 30 minutes, and this continuation uses at most 12 concurrent computational workers.', '',
              'Every assigned case is attempted in dimension order, with a barrier between dimensions. Searches checkpoint after every configuration and preserve every complete certificate atomically, including certificates from incomplete covers. Escalation reuses complete files, never partial trees. `input_*.json`, `search_*.json` and logs record budgets, schedules, code hashes, frontiers and stopping reasons.', '',
              'A late runtime check found that the historical default forkserver pool did not inherit the parent process\'s cross-stage certificate index. Same-stage files could be reused, but the cross-stage cache was ineffective, causing redundant work. All generated files were retained and directly checked. The driver now requests a fork context explicitly; an actual search-worker test confirms hash-protected cache reuse (`cache_test_results.json`). A final bounded cache-recovery pass targets only unfinished configurations that had already saved complete pieces (`recovery_selection.json`); it does not relax certificate or coverage checks. Historical timings and certificate counts include the redundant work.', '',
              'The hybrid refinement is already the nd-sym representation: each distinct coefficient is a separate group/coordinate, and each repeated-coefficient group is a multiset. Only permutations within an equal-coefficient group are identified. Distinct coefficient groups are never exchanged, so every distinct far coefficient ordering is covered. Each CLOSED configuration records its number of distinct coefficient words, k! / product(m_c!), in the coverage ledger.', '',
              f'An additional independent combinatorial audit enumerates all {orderings["total_distinct_orderings"]} distinct coefficient words over the {len(orderings["configurations"])} assignments. For each word it verifies the bijection to coefficient-group position ranks and back, with no exchanged or lost distinct coefficients. Replacing ranks by arbitrary increasing positions proves coverage of each entire ordering cone. Per-configuration counts and word-stream hashes are in `ordering_audit.json`.', '',
              '`gen_precomputed.py` adds search-only memoization and precomputes the decimal orbit {10^(g*j) mod p}, where g=gcd(M,ord_p(10)). Each coefficient contribution is its exact residue coset c*10^(q mod g) times this orbit. The existing independent sumset overapproximation and unchanged checker establish acceptance. Cached forbidden tests retain both exact exponent signatures; free lower bounds may be omitted from the key only with decimal-tail cosets, whose finite subgroup image is independent of the lower bound. `precompute_test_results.json` records equivalence and exact orbit checks.', '',
              'Every retained certificate, including partial-cover components and inherited components actually reused, is replayed by a direct subprocess invocation of copied `check_sym.py` with brute L<=10. The checker is invoked as a CLI, without a wrapper import or monkeypatch. Commands, hashes, verdicts and timings are in `standalone_checks.json`. All retained certificates use nd-sym format, so the legacy-format condition for `verification/v14_checknd_hd.py` is inapplicable; no legacy-format certificate is presented as dual-checked.', '',
              'Configuration closure is independently recomputed by the copied `audit_coverage.cover`, using only full-domain, hash-bound PASS certificates. If its enlarged cover is incomplete, a second independent replay in `coverage_distinct.py` tracks already fixed positions and discards a low branch only when that position is already fixed. Such a branch contradicts the original pairwise-distinct position domain. All viable low values and the high tail remain covered; free/free and free/fixed collision restrictions are still relaxed inside certificates. The state includes the fixed-position set, so different fixed sets are never silently merged. Per-closure coverage methods and skipped-branch counts are recorded. This is a coverage refinement, not a new arithmetic kill type.', '',
              'For the higher-dimensional strong-floor pass, slicing instead decides successive positions p=3,4,...: either the position is empty (digit 1), or it contains one of the distinct remaining coefficient values, which is added to K and removed from the multiset. Advance p once in either case. Stop only when p >= max(3,v2(K)+3), and emit the remaining domain at floor p. Each original placement follows exactly one branch, positions cannot be fixed twice, and every coefficient ordering is covered. `position_cover` independently replays this containment from checked domains. A terminal certificate covers L>=p; all smaller lengths are included in the finite exception scan. Position-by-position slicing is also independently justified in Agent F\'s coverage write-up.', '',
              f'The distinct-fixed-position splitting invariant passes {cover_tests["cases"]} independent small-box comparisons covering {cover_tests["labelled_points"]} labelled distinct points, including lengths below terminal floors. A separate exact enumeration of all 2/3/7-smooth integers below the largest finite exception bound checks the omitted short lengths. All size-leaf solutions are filtered back to the original target, low digits and far coefficient multiset; closure means a complete member list, not necessarily emptiness.', '',
              f'The position-by-position splitting invariant separately passes {cover_tests["position_partition"]["cases"]} small-box comparisons covering {cover_tests["position_partition"]["canonical_points"]} canonical points. Coverage method counts are `{summary["coverage_methods"]}`.', '',
              '## Executed results', '']
    for target, dims in summary['counts_by_target_dimension'].items():
        for dim, rec in dims.items():
            lines.append(f'- Target {target}, dimension {dim}: {rec["closed"]} closed, {rec["open"]} still open, {rec["assigned"]} assigned.')
    lines += ['', f'Direct checker verdicts: {summary["checker_counts"]}. New retained search certificates: {summary["new_certificates"]}; inherited components directly replayed again: {summary["inherited_certificates_replayed"]}; additional control/smoke files: {summary["control_certificates_replayed"]}.', '',
              f'The finite exception scan checks {summary["finite_exception_scan"]["smooth_points"]} smooth integers through {summary["finite_exception_scan"]["Lmax"]} digits, finding {len(summary["finite_exception_scan"]["members"])} members in the closed configurations. The complete member list is in `summary.json`.', '',
              'Per-certificate kill dependencies and counts are in `kill_usage.json`; per-configuration unions are in `summary.json`. Dependencies conservatively include decimal-tail or mod-8 constraints whenever enabled and prime references occur, even if an individual witness could be reproved without them. Unaligned prime references are sumset kills; aligned references are ordinary residue/coset kills. Counts below count certificate dependencies or stored references, not omitted residue classes.', '',
              f'Alignment labels use independently verified exact decimal orders (stored per prime), with supply orders treated as untrusted hints. The order/classification helper passes {label_tests["classification_cases"]} comparisons against finite decimal cycles, including exact, nonminimal, invalid and missing hints.', '',
              f'All retained/reused certificate dependency counts: `{summary["certificate_dependency_counts"]}`.', '',
              f'All retained/reused stored reference counts: `{summary["certificate_reference_counts"]}`.', '',
              f'Certificates actually used in full closures: {summary["closure_certificate_count"]}; dependency counts: `{summary["closure_dependency_counts"]}`; reference counts: `{summary["closure_reference_counts"]}`.', '',
              'Agent F audit evidence seen at finalization is hash-listed in `summary.json` under `auditor_files`. If this list is empty, no indep4 report was present in this checkout. Checker acceptance is recorded separately from any independent soundness audit. A later invalidated kill type can be mapped to every affected certificate and configuration through these dependency ledgers.', '',
              f'Agent F independently confirms {auditor["results"].get("PASS", 0)}/{auditor["certs"]} prior sym certificates and reports no unsound kill type. Its verdict/proofs/coverage text and summary are frozen under `inputs/indep4/`. This is confirmation of the prior closures and kill-type arguments; it is not represented as an F-checker replay of the new sym2 certificates.', '',
              '## Checkpointed search stages', '']
    for stage, rec in stages.items():
        lines.append(f'- `{stage}`: {rec["configurations"]} attempts; {rec["statuses"]}; {rec["worker_seconds"]} worker seconds; {rec["partial_lifts"]} partial lifts plus {rec["completed_lifts"]} completed-job lifts.')
    lines += ['', '## Exact final still-open set', '', '```text', *summary['open'], '```', '',
              'The exact newly closed set, complete slice covers, member lists, coefficient ordering counts and kill dependencies are in `summary.json`. `manifest.json` hashes the evidence and this note. All search BUDGET diagnostics are finite computation records, not impossibility claims.', '',
              '## Direct reproduction commands', '', '```sh',
              "bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym2/continue_sym2.py reconcile'",
              "timeout 1500 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym2/continue_sym2.py check --workers 12 --force-check'",
              "timeout 1500 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym2/continue_sym2.py audit'",
              "bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym2/finalize_sym2.py'",
              "bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym2/verify_manifest.py'", '```', '']
    note = ROOT / 'notes/highdim_sym2.md'
    note.write_text('\n'.join(lines))
    manifest = {str(p.relative_to(HERE)): digest(p) for p in sorted(HERE.rglob('*'))
                if p.is_file() and p.name != 'manifest.json' and p.suffix not in ('.log', '.tmp') and '__pycache__' not in p.parts}
    manifest['../../../notes/highdim_sym2.md'] = digest(note)
    (HERE / 'manifest.json').write_text(json.dumps({'sha256': manifest, 'excludes': ['*.log', '*.tmp', '__pycache__']}, indent=1) + '\n')
    print(json.dumps({'counts': summary['counts_by_target_dimension'], 'checker_counts': summary['checker_counts'], 'manifest_files': len(manifest)}))


if __name__ == '__main__':
    main()
