import json, hashlib
from pathlib import Path
from collections import Counter
root=Path('research'); paths=[root/'experiments/H004/coverage_initial_results.json',root/'experiments/H004/coverage_gate.py',root/'hypotheses/H004-progression-coverage-protocol.md']
expected=['118bc3cda44688cfbeb12267524f494fdb17ef26e9d2f92d156374aa8db3b19b','8922240d5f2eabf7e9113122cac849210cf573e9a666f19b26c41b82f28b285b','011ee6254fcd39829a862552047ad016d82317f6925813497b1ab9ec8e24ab80']
assert [hashlib.sha256(p.read_bytes()).hexdigest() for p in paths]==expected
D=json.loads(paths[0].read_text()); assert D['source_sha256']==expected[1]
assert [p['q'] for p in D['profiles']]==[31,61,127,251,509]
assert D['status']=='incomplete_budget_stop' and not D['complete']
total=Counter(); completed=0; hitrows=0; partial=[]
for p in D['profiles']:
 q=p['q']; m=p['ceil_sqrt_q']; N=p['prefix_cap']; F=p['fallback_description']['full_output_count_F']
 assert (m-1)**2<q<=m*m and N==2*m+4 and F==2*(m+1)
 subtotal=Counter(p['setup_event_vector']); decl=p['declared_deduplicated_configs']
 assert len(decl)==13
 for c in decl:
  M=c['M']; kind=c['kind']
  if kind=='candidate_P1':
   assert 2*M*M<=q<2*(M+1)**2
   assert (c['b'],c['s'],c['cycle'])==([0,1,2,3],[1,M,-M-1,2*M+1],[0,1,2,3])
  else:
   for g in c['coincident_parameters']:
    u,v=g['c_numerator'],g['c_denominator']; assert [u,v] in D['baseline_c_grid']
    assert 2*v*v*M*M<=u*u*q<2*v*v*(M+1)**2
   if kind=='baseline2': assert (c['b'],c['s'],c['cycle'])==([0,1],[1,-M],[0,1])
   else: assert c['b']==[0,1,2] and c['s']==[1,M,-M] and c['cycle'] in ([0,1,2],[0,0,1,2])
 for index,c in enumerate(p['configs']):
  assert c['parameters']==decl[index]
  if not c['complete']:
   assert c['phase']=='emissions' and 'prefix_mean' not in c and 'hit_histogram' not in c
   subtotal.update(c['partial_event_vector']); partial.append((q,c['parameters']['id'],c['emissions'],len(c['labels']),c['covered'])); continue
  completed+=1; hitrows+=q; ts=c['hit_time']; assert len(ts)==q and ts[0]==0
  assert all(t is None or isinstance(t,int) and 0<=t<=c['emissions']<=N for t in ts)
  fail=ts.count(None); hist=Counter('uncovered_at_cap' if t is None else str(t) for t in ts)
  assert dict(hist)==c['hit_histogram'] and fail==c['failures'] and q-fail==c['covered']
  S=sum(N if t is None else t for t in ts)
  assert c['prefix_mean']=={'numerator':S,'denominator':q}
  assert c['fallback_output_charge']==F*fail
  assert c['prefix_plus_fallback_mean']=={'numerator':S+F*fail,'denominator':q}
  assert (fail==0)==(c['coverage_stop']=='all_scalars_covered')
  assert len(c['labels'])==c['emissions']; ev=c['event_vector']
  assert ev['emissions']==c['emissions'] and ev['metric_passes']==q and ev['coverage_array_initializations']==q
  assert ev['collision_equation_processing']==c['scalar_equations']+c['zero_denominator_tautologies']+c['zero_denominator_contradictions']
  assert ev['identity_processing']==c['identity_equations']; subtotal.update(ev)
 if p['complete']:
  refs=Counter()
  for kind in ('baseline2','baseline3'):
   for metric in ('prefix_mean','prefix_plus_fallback_mean'):
    best=None; ids=[]
    for c in p['configs']:
     refs['reference_metric_passes']+=1; refs['comparisons']+=1
     if c['parameters']['kind']!=kind: continue
     x=c[metric]['numerator']
     if best is not None: refs['comparisons']+=1
     if best is None or x<best: best=x; ids=[c['parameters']['id']]
     else:
      refs['comparisons']+=1
      if x==best: ids.append(c['parameters']['id'])
    assert p['reference_grid_minima_only'][kind][metric]=={'numerator':best,'denominator':q,'minimizing_config_ids':ids}
  subtotal.update(refs); assert subtotal==Counter(p['event_vector'])
 else: assert 'reference_grid_minima_only' not in p
 total.update(subtotal)
 a=p['configs'][0]; b=next(c for c in p['configs'] if c['parameters']['id']=='baseline2_4')
 assert a['complete'] and b['complete'] and b['failures']==0
 assert b['parameters']['coincident_parameters']==[{'M':b['parameters']['M'],'c_numerator':2,'c_denominator':1}]
 assert a['prefix_mean']['numerator']>b['prefix_plus_fallback_mean']['numerator']
 print('COMPARISON',q,'P1_censored',a['prefix_mean']['numerator'],'P1_fallback',a['prefix_plus_fallback_mean']['numerator'],'B2',b['prefix_plus_fallback_mean']['numerator'],'P1_tail',a['failures'])
assert total==Counter(D['charged_event_vector']) and sum(total.values())==D['total_events']==1000000
assert completed==D['completed_configs']==58 and sum(p['complete'] for p in D['profiles'])==D['completed_profiles']==4
assert partial==[(509,'baseline3_6',44,44,231)]
print('PASS',completed,'complete configs;',hitrows,'complete hit rows; exact global vector reconciliation; partial',partial)
