"""Write the executed-results note and hash manifest; stdlib only."""
import sys
sys.dont_write_bytecode = True
import collections
import hashlib
import json
import pathlib

H = pathlib.Path(__file__).resolve().parent
R = H.parents[2]

def load(p):
    return json.loads(p.read_text())

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    s = load(H / 'summary.json')
    checks = load(H / 'checks5.json')
    assert load(H / 'slice_domain_audit.json')['result'] == 'PASS'
    assert not s['failed_certificates']
    assert all(r['M']['result'] == 'PASS' for r in checks['files'].values())
    for path, records in checks['files'].items():
        depth = json.loads(pathlib.Path(path).open().readline()).get('pin_digits', 0)
        if depth <= 3: assert records['F']['result'] == 'PASS'
        elif checks['F5_available']: assert records['F5']['result'] == 'PASS'
    assert s['all_60_attempted'] and s['all_unfinished_escalated']
    for p, digest in load(H / 'source_hashes.json').items():
        assert sha(R / p) == digest, p
    note = R / 'notes/highdim_sym6.md'
    text = note.read_text().split('Search and validation are in progress.')[0].split('\n## Executed results')[0].rstrip() + '\n'
    text += '\n## Executed results\n\n'
    for k, row in sorted(s['counts_by_k'].items(), key=lambda kv: int(kv[0])):
        text += '- k=%s: %s closed, %s open; %s closures require a deep pin in the retained library; %s independently checked covers.\n' % (
            k, row['closed'], row['open'], row['deep_pin_closures'], row['independently_checked'])
    text += '\nTotal: **%d closed, %d open**, with **%d deep-pin closures**.\n' % (
        len(s['closed']), len(s['open']), s['deep_pin_closures'])
    text += ('Deep-pin counts mean that the retained certificate library does not provide a complete depth-at-most-three cover. '
             'Every deep tree was also tried with the same tree at depth three; successful downgrades received a fresh original-F replay. '
             'This does not claim that another depth-three proof is impossible.\n\n')
    text += 'Fresh direct checker results on all original retained/search certificates: `%s`.\n\n' % s['checker_counts']
    text += 'Depth-three same-tree attempts: `%s`; original-F results including successful downgrades: `%s`.\n\n' % (
        s['downgrades'], s['original_F_including_downgrades'])
    discarded_path=H/'discarded_ablation_candidates.json'
    discarded=load(discarded_path) if discarded_path.exists() else []
    if discarded:
        text += ('%d depth-three candidates did not obtain independent F acceptance and were deleted from the retained certificate directory. '
                 'Their complete replay failures are preserved in `discarded_ablation_candidates.json`; the original deep certificates remain checked.\n\n') % len(discarded)
    text += 'Closure certificates: %d; retained deep closure certificates: %d.\n\n' % (
        s['closure_certificates'], s['closure_deep_certificates'])
    if checks['F5_available']:
        text += ('The F5 readiness note exists and reports passing tests. Every deep certificate received a fresh direct F5 PASS, '
                 'and the complete M/F5 solution lists agree. All counted covers have independent checker confirmation.\n\n')
    else:
        text += ('**Independent deep-pin replay is pending.** At the final availability check, F5 did not have the required readiness note '
                 'reporting passing tests. Counts use direct sym5 checks and independently replayed covers; they do not imply F5 confirmation. '
                 '`deep_pin_certs.txt` lists all deep search certificates, and `closure_deep_pin_certs.txt` lists the retained closure subset.\n\n')
    text += 'Ordering audit: **%s**, all 60 configurations and %d coefficient words. Coverage: **%d complete, %d incomplete**.\n\n' % (
        s['ordering_result'], s['total_distinct_orderings'], len(s['closed']), len(s['open']))
    text += ('`coverage_audit.json` records every case, its complete cover or missing-domain diagnostics, all coefficient-ordering counts, '
             'and the finite exception bound. `slice_domain_audit.json` verifies every checkpointed slice against its retained certificate domain and hash. `v2_inventory.json` independently lists all canonical v2 branches, including those in open cases. '
             'No incomplete cover is counted closed.\n\n')
    text += 'Finite smooth scan: `%s`. All size-leaf solutions were filtered back to their original digit configurations.\n\n' % s['finite_exception_scan']
    text += 'Kill-type ledger dependency totals: `%s`; stored witness references: `%s`.\n\n' % (
        s['kill_dependency_counts'], s['kill_reference_counts'])
    text += 'Copied arithmetic and partition controls: `%s`.\n\n' % {
        k: v for k, v in s['test_results'].items() if k not in ('genuine_size_solution', 'enumerated_pairs')}
    for name, stage in s['stages'].items():
        text += '- `%s`: %d attempts, `%s`, %.3f worker seconds.\n' % (
            name, stage['attempts'], stage['statuses'], stage['worker_seconds'])
    text += ('\nEvery still-unfinished configuration received the next stage. Completed slices from unfinished configurations were retained '
             'and checked too; partial trees were never emitted. OPEN means a bounded search did not produce a checked complete cover.\n\n')
    text += 'Reproduction from the repository root (each command bounded below thirty minutes):\n\n```sh\n'
    for p in sorted(H.glob('input_*.json'), key=lambda p: p.stat().st_mtime):
        a = load(p)
        stage = p.stem.removeprefix('input_')
        text += ("timeout 1200 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym6/continue_sym2.py search "
                 '--stage %s --seconds %s --workers %s --pin-digits %s --position-slices --precompute --schedule %s '
                 "--extra-floor %s --modulus-digits %s --depth %s'\n") % (
                     stage, a['seconds_per_configuration'], a['workers'], a['pin_digits'], a['schedule'], a['extra_floor'], a['modulus_digits'], a['depth'])
        if a.get('mixed_dimensions'): text = text[:-2] + " --mixed-dimensions'\n"
    text += "timeout 600 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym6/test_sym5.py'\n"
    text += "timeout 1500 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym6/replay5.py --workers 10 --seconds 900 --brute 11 --downgrade'\n"
    text += "timeout 600 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym6/prune_ablations6.py'\n"
    text += "timeout 600 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym6/audit_search_domains6.py'\n"
    text += "timeout 900 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym6/finalize5.py'\n"
    text += "timeout 600 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym6/seal6.py'\n```\n\n"
    text += ('Evidence under `verification/highdim/sym6/`: `assignment.json`, `summary.json`, `coverage_audit.json`, `ordering_audit.json`, '
             '`v2_inventory.json`, `kill_usage.json`, `checks5.json`, `checks5_journal.jsonl`, `test_results.json`, `source_hashes.json`, '
             '`manifest6.json`, `input_*.json`, `search_*.json`, `closure_certs.txt`, `deep_pin_certs.txt`, `closure_deep_pin_certs.txt`, '
             '`certs/`, and `k3_certs/`. All passes are fresh direct CLI invocations; no inherited checker PASS was reused. '
             'Source hashes verified unchanged. No git commit was made.\n')
    note.write_text(text)
    external = {}
    for path, rec in checks['files'].items():
        external[path] = rec['M']['sha256']
        for label in ('M', 'F', 'F5'):
            if label in rec:
                external[rec[label]['command'][4]] = rec[label]['checker_sha256']
        ab=rec.get('downgrade',{})
        if 'file' in ab:
            for label in ('M','F'):
                external[ab[label]['command'][4]]=ab[label]['checker_sha256']
    ready = checks.get('F5_readiness_note', {})
    if ready.get('exists'):
        external[ready['path']] = ready['sha256']
    manifest = {'files': {str(p.relative_to(R)): sha(p) for p in sorted(H.rglob('*'))
                          if p.is_file() and p.name != 'manifest6.json' and not p.name.endswith('.tmp')},
                'external_certificates_and_checkers': external,
                'note': {str(note.relative_to(R)): sha(note)}}
    for p, digest in external.items():
        assert sha(pathlib.Path(p)) == digest, p
    (H / 'manifest6.json').write_text(json.dumps(manifest, indent=1) + '\n')
    print(json.dumps({'result': 'PASS', 'counts_by_k': s['counts_by_k'], 'manifest_files': len(manifest['files'])}))

if __name__ == '__main__':
    main()
