import pathlib,json,hashlib,re,zipfile
lane=pathlib.Path(__file__).resolve().parent.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mods={p.name:{'sha256':sha(p),'lines':len(p.read_text().splitlines()),'frozen_round1':not p.name.startswith('StackSortInj2')} for p in sorted(lane.glob('*.lean'))}
for name,m in mods.items():
 assert sha(lane/'fresh-extraction'/name)==m['sha256']
 if m['frozen_round1']:assert sha(lane.parent/'stacksort-formal-r1'/name)==m['sha256']
assert (lane/'input-before.sha256').read_bytes()==(lane/'input-after.sha256').read_bytes()
fresh=lane/'fresh-extraction'
order=(lane/'scripts/order.txt').read_text().split()
checks={}
for kind in ['replay-build','checker']:
 for m in order:
  p=fresh/'logs'/f'{kind}-{m}.log'
  assert p.is_file(),p
  s=p.read_text()
  assert re.search(r'\nexit 0\n',s),str(p)
  checks[f'{kind}:{m}']=str(p.relative_to(lane))
audit=json.loads((fresh/'audit-summary.json').read_text())
for name in ['audit-summary.json','compiler-symbols.json']:
 (lane/name).write_bytes((fresh/name).read_bytes())
assert audit['closure_equals_audited_set']
logs=list((lane/'logs').glob('*.log'))+list((fresh/'logs').glob('*.log'))
maxrss=max([int(v) for p in logs for v in re.findall(r'Maximum resident set size \(kbytes\): (\d+)',p.read_text())])
assert maxrss<6*1024*1024
assert not any('RSS CAP EXCEEDED' in p.read_text() for p in logs)
r={'status':'PARTIAL_NOT_ACCEPTED','self_accepted':False,'credit':0,'round':'2A','mathdb_id':345545,
'lean':'4.34.1','mathlib':'d13f23b723b8a846827a245b89c10fc7d3f11612','modules':mods,
'frozen_modules_byte_identical':True,'frozen_module_count':11,
'frozen_archive_sha256':sha(lane.parent/'stacksort-formal-r1/stacksort-source.zip'),
'completed':['factorial conversion DoublingInjection → Doubling','rootGlue inverse and increasing-relabelling validity','fixed label block injection P a * P b ≤ P(a+b+1)','four disjoint end families 4 P n ≤ P(n+1) for n>0','computable structural G and its equations','RootSplit → ExactSeeds20 → ∀ n, G n ≤ P n','110 kernel checked lower rows','G 130 = lower130','RootSplit → ExactSeeds20 → Lower130'],
'Props_closed_unconditionally':[],
'Props_reduced':{'Doubling':'DoublingInjection → Doubling','Lower130':'RootSplit → ExactSeeds20 → Lower130'},
'remaining_Props':{'DoublingInjection':'∀ a : ℕ, Nat.choose (2*a) a * P a ^ 2 ≤ P (2*a+1)','RootSplit':'∀ n : ℕ, 2 ≤ n → 4*P(n-1) + ∑ i ∈ Finset.Icc 1 (n-2), Nat.choose (n-1) i * P i * P(n-1-i) ≤ P n','ExactSeeds20':'∀ n : ℕ, 1 ≤ n → n ≤ 20 → P n = seed20[n]!; reserved to lane 2B'},
'endpoints':{'StackSort.Inj2.mathdb_345545':'CONDITIONAL on DoublingInjection, RootSplit, ExactSeeds20','StackSort.Inj2.limit_ge':'same three Props','StackSort.Inj2.nonvacuity':'same three Props','StackSort.Inj2.subsequence_companion':'same three Props; index 130 k + 1 = 131*2^k','StackSort.mathdb_345545_max':'UNCONDITIONAL frozen round 1'},
'requested_only_ExactSeeds20_endpoint_completed':False,
'fresh_replay':{'strict_serial_compilation':True,'leanchecker_every_module':True,'module_count':len(order),'checks':checks},
'audit':audit,'negative_controls':['frozen wrong seed','frozen wrong convention','frozen wrong threshold 1.95','frozen wrong base129','wrong_G_seed_rejected','wrong_lower_row_rejected'],
'archive':{'path':'stacksort-source.zip','sha256':sha(lane/'stacksort-source.zip'),'safe_paths':True,'source_only':True},
'resources':{'all_Lean_and_Python_and_leanchecker_calls_wrapped':True,'RSS_watchdog_limit_KiB':6291456,'max_observed_RSS_KiB':maxrss,'CPU_limit_seconds_per_call':120,'wall_limit_seconds_per_call':140,'CPUs':[0,1],'MALLOC_ARENA_MAX':2,'Lean_memory_limit_MB':3500,'watchdog_kills':0},
'background_jobs_remaining':False,'next_round_plan':'PROOF.md','summary':'SUMMARY.md'}
assert r['frozen_archive_sha256']=='67a3893f3a08616fe9d4480ce28b166cbf410df5d9edf4ca5ccb054340253dde'
(lane/'results.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ['status','frozen_module_count','Props_closed_unconditionally','archive','resources']},indent=2))
