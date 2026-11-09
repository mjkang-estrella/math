"""Freeze final evidence and append computed results to the research note."""
import sys
sys.dont_write_bytecode=True
import collections,hashlib,json,pathlib
H=pathlib.Path(__file__).resolve().parent;R=H.parents[2]
def read(p):return json.loads(pathlib.Path(p).read_text())
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def save(p,o):
 t=p.with_suffix(p.suffix+'.tmp');t.write_text(json.dumps(o,indent=1)+'\n');t.replace(p)
def main():
 summary=read(H/'summary.json');checks=read(H/'dual_checks.json');audit=read(H/'coverage_audit.json');ledger=read(H/'kill_ledger.json');supply=read(H/'prime_supply_audit.json')
 assert summary['all_certificates_dual_checked'] and all(r[w]['result']=='PASS' for r in checks.values() for w in ('M','F5'))
 assert set(checks)=={str(p) for p in (H/'certs').glob('*.jsonl')}
 for f,d in read(H/'source_hashes.json').items():assert sha(f)==d,('original changed',f)
 for f,rs in checks.items():
  for w,r in rs.items():assert r['sha256']==sha(f) and r['checker_sha256']==sha(r['command'][4])
 stages={}
 for p in sorted(H.glob('search_*.json')):
  d=read(p);stages[p.stem]={'attempts':len(d),'statuses':dict(collections.Counter(v['status'] for v in d.values())),'worker_seconds':round(sum(v['seconds'] for v in d.values()),3),'states':sum(v['states'] for v in d.values()),'open_leaves':sum(v['open_leaves'] for v in d.values())}
 added={r[0] for r in supply['added']};used_added=collections.Counter()
 for r in ledger.values():
  for p,v in r['primes'].items():
   if int(p) in added:used_added[p]+=v['references']
 depths=collections.Counter(str(v['pin_digits']) for v in ledger.values());kills=collections.Counter()
 for v in ledger.values():kills.update(v['kills'])
 closed_domains=sorted({f for name in summary['closed'] for f in summary['configurations'][name]['domains']})
 (H/'closure_certs.txt').write_text(''.join(f+'\n' for f in closed_domains))
 stats={'stages':stages,'tree_count':len(audit['trees']),'audited_states':sum(t['states'] for t in audit['trees']),'peeling_splits':sum(t['peeling_splits'] for t in audit['trees']),'certificates':len(checks),'pin_depths':dict(depths),'kill_references':dict(kills),'added_prime_witness_references':dict(used_added),'closure_certificates':len(closed_domains),'closure_pin_depths':dict(collections.Counter(str(ledger[f]['pin_digits']) for f in closed_domains)),'original_hashes_unchanged':True,'stale_records_reconciled':len(read(H/'stale_hash_incident.json')['stale_records'])}
 save(H/'research_stats.json',stats)
 note=R/'notes/highdim_sym7a.md';body=note.read_text().split('\n## Executed results\n')[0]
 rows='\n'.join('| %s | %d | %d | %d |'%(d,r['assigned'],r['closed'],r['open']) for d,r in summary['counts_by_dimension'].items())
 text=f'''
## Executed results

Counts below refer only to the 33 assigned sym5-open configurations, all for
target 14112. **1 closed, 32 open.**

| Dimension | Assigned | Closed | Open |
|---|---:|---:|---:|
{rows}

The closure is `14112:623|9,9,9,18,54`. Its retained cover has
{len(closed_domains)} directly dual-checked certificate domains. Closure pin depths:
`{stats['closure_pin_depths']}`. OPEN records explicitly retain unresolved
slices; no smooth member was discovered, and no claim of impossibility is
made for those 32 configurations.

**Direct checker results:** sym5 `check_sym5.py`: **{len(checks)}/{len(checks)} PASS**;
independent `check_sym_F5.py`: **{len(checks)}/{len(checks)} PASS**. Both were invoked
directly on every retained certificate, with brute bound 11 and 8,000,000 KiB
virtual-memory limits. No large-memory exception was needed. No current
certificate/checker hash is stale, and no FAIL, TIMEOUT or pending result is
used. Original source hashes and byte-identical archival copies are checked.

**Coverage:** PASS for the exhaustive partitions in all {stats['tree_count']}
recorded trees: {stats['audited_states']} states and {stats['peeling_splits']} peeling splits.
The accepted complete cover closes the dimension-6 configuration. Every other
cover retains an explicit OPEN leaf. The finite controls passed 84 cases /
1,260 canonical points, with exact equality and disjointness against direct
original-assignment enumeration. The separate finite scan through length
{summary['finite_scan']['Lmax']} enumerated {summary['finite_scan']['smooth_points']} smooth
numbers and found **zero matching members** across the assigned configurations.
The auditor independently reconstructs split children rather than trusting
the driver's claimed coverage.

Certificate depths are `{stats['pin_depths']}`. The ledger records every
auxiliary prime reference, supplied order annotation, aligned versus sumset
prime leaf, exact-size leaf, valuation, pin setting, digest and dual-check
status. Full independently recomputed arithmetic statistics and any declared
solutions are retained in the checker records. Kill-reference totals:
`{stats['kill_references']}`. A rest reference denotes a witness listed at a
refinement; it is not a claim of that many distinct killed classes.

The bounded supply search considered {supply['tried']} candidates and added
{supply['added_count']} primes to the 1,621-entry copied supply. Added-prime
witness references in retained certificates: `{dict(used_added)}`. No closure
gain is attributed to the expanded supply: the successful dimension-6 cover
was obtained before that experiment. The targeted dimension-7 floor-8 run
still leaves `(K=188, C=[9,9,18,27,54,54], qmin=8)` unresolved. Its final attempt
stopped at the five-million-lift cap; floor-7 attempts also hit modulus or
lift limits. This is a search limitation, not a counterexample or rejection
of position peeling.

### Checkpoint and cache incident

The first implementation assumed workers inherited the prepared certificate
library. This Python version uses a different default multiprocessing start
method, so the library was absent inside workers. The first pass still
constructed sound peeling covers, but later uncached runs regenerated some
files. The audit detected {stats['stale_records_reconciled']} stale hash-bound checker records.
The correction selects an explicit fork context, publishes certificates
immutably with atomic hard links, and requires matching hashes when deciding
whether to skip a replay. All affected current files received fresh direct
replays; all {len(checks)} final file hashes now match both PASS records. The incident
and obsolete hash records remain in `stale_hash_incident.json` and the
append-only checker journal. Final `dual_checks.json` is the authority.
The corrected cache was exercised in `peel8cached`: all 104 terminal
certificates were reused and the single unresolved root was reattempted.

### Search stages

'''
 text+='| Stage | Configurations | Candidate covers | Open | Worker seconds |\n|---|---:|---:|---:|---:|\n'
 for stage,rec in stages.items():text+='| %s | %d | %d | %d | %.3f |\n'%(stage,rec['attempts'],rec['statuses'].get('CANDIDATE',0),rec['statuses'].get('OPEN',0),rec['worker_seconds'])
 text+='''
Candidate covers are search output only; the counts above use direct dual
replay plus the independent coverage and finite scan. Search failures never
emit partial certificate trees. All 33 received the full initial bounded
pass. Later experiments deliberately targeted the almost-complete dimension-7
cover rather than claiming an exhaustive larger-budget pass.

### Reproduction and continuation

The final driver defaults to the original sym5 adaptive refinement cycle.
Use `--rich-five` to select `(2,3,5,2,3,5,2,7)` instead. The sole generator
diff is a search-order option; the certificate format and arithmetic kills
are unchanged. `gen_sym_baseline.py` preserves the byte-identical sym5 source.
Initial stages before the cache fix are retained as historical checkpoints;
rerunning with a fresh stage name uses the corrected cache and can perform
different amounts of work within the same wall-clock budget.

```sh
# A new bounded all-assignment continuation, using existing immutable files:
timeout 1200 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym7a/run7a.py --stage resume7 --floor 7 --seconds 90 --slice-seconds 3 --workers 8'
# The targeted floor-8 / factor-five experiment, using a fresh stage name:
timeout 300 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym7a/run7a.py --stage resume8five --key "14112:21|9,9,18,27,54,54" --floor 8 --seconds 120 --slice-seconds 25 --workers 1 --schedule 2,3,5,2,3,5,2,7 --rich-five'
# Run after search completes; do not exceed ten combined search/replay workers:
timeout 1500 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym7a/replay7a.py --workers 8 --timeout 300'
timeout 180 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym7a/audit7a.py'
timeout 180 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym7a/report7a.py'
```

Main evidence under `verification/highdim/sym7a/`: `summary.json`,
`coverage_audit.json`, `kill_ledger.json`, `dual_checks.json`,
`dual_journal.jsonl`, `research_stats.json`, `closure_certs.txt`,
`partition_controls.json`, `source_hashes.json`, `prime_supply_audit.json`,
`tree_*.json`, `input_*.json`, `search_*.json`, and `certs/`.
`manifest7a.json` binds the final note, scripts, ledgers, inputs, trees, and
all certificates. No original sym5/indep5 file was modified and no commit
was made.
'''
 note.write_text(body+text)
 paths=[p for p in H.rglob('*') if p.is_file() and p.name!='manifest7a.json' and not p.name.endswith(('.log','.tmp'))]+[note]
 save(H/'manifest7a.json',{'files':{str(p):sha(p) for p in sorted(paths)},'scope':'all sym7a evidence except logs and manifest itself; includes research note','certificate_count':len(checks)})
 print(json.dumps(stats))
if __name__=='__main__':main()
