import pathlib,json,hashlib,re
lane=pathlib.Path(__file__).resolve().parent.parent
modules={p.name:{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'lines':len(p.read_text().splitlines())} for p in sorted(lane.glob('StackSort*.lean'))}
audit=json.loads((lane/'fresh-extraction/audit-summary.json').read_text())
checks={}
for p in sorted((lane/'fresh-extraction/logs').glob('*.log')):
 t=p.read_text();first=t.splitlines()[0];last=t.strip().splitlines()[-1]
 checks[first]={'log':str(p.relative_to(lane)),'exit':int(last.split()[1])}
assert all(c['exit']==0 for c in checks.values())
assert len([k for k in checks if k.startswith('leanchecker ')])==11
assert len([k for k in checks if k.startswith('lean ')])==11
r={'mathdb_id':345545,'status':'PARTIAL_NOT_ACCEPTED','self_accepted':False,'credit':0,
'lean':'4.34.1','mathlib':'d13f23b723b8a846827a245b89c10fc7d3f11612','modules':modules,
'endpoints':{'mathdb_345545':'CONDITIONAL on Doubling and Lower130','limit_ge':'CONDITIONAL on Doubling and Lower130','nonvacuity':'CONDITIONAL on Doubling and Lower130; explicit index 131*2^k-1','mathdb_345545_max':'UNCONDITIONAL_PROVED','max_companion':'UNCONDITIONAL_PROVED for every n >= 5'},
'completed_route':['L1','L2','L4','L5 conditional on L3 and base bound','integer certificate at 130','maximum-fibre reading'],
'remaining_Props':{'Doubling':'∀ a : ℕ, deg a ^ 2 ≤ (2 * a + 1 : ℝ) * deg (2 * a + 1)','Lower130':'lower130 ≤ P 130'},
'open_intermediate_Props':['DoublingInjection','RootSplit','ExactSeeds20'],
'not_remaining':['Standardisation (proved)','MaxFamilyBound (proved by max_family_bound)'],
'kernel_literal_regressions':{'completed_through':4,'P5':'memory limit; not claimed','P6':'not completed'},
'python_regression':{'literal_through':8,'topmax_exact_through':20,'lower_recursion_through':130,'is_combinatorial_proof':False},
'negative_controls':'four kernel-checked rejection theorems in StackSortControls.lean and four Python controls',
'fresh_replay':{'safe_source_only_zip':True,'empty_extraction':True,'strict_compilation':True,'leanchecker_every_module':True,'checks':checks},
'audit':audit,'archive':{'path':'stacksort-source.zip','sha256':hashlib.sha256((lane/'stacksort-source.zip').read_bytes()).hexdigest()},
'resource_compliance':False,'resource_exception':{'command':'leanchecker --help','peak_rss_KiB':12694900,'reason':'unknown flag ignored; no target caused whole-search-path scan','terminated':True,'correction':'explicit modules and RSS watchdog'},
'background_jobs_remaining':False,'next_round_plan':'PROOF.md','summary':'SUMMARY.md'}
(lane/'results.json').write_text(json.dumps(r,indent=2)+'\n')
print('PARTIAL; fresh replay checks',len(checks),'all pass; local declarations',audit['local_declarations'])
