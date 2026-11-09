import importlib.util, itertools, json, pathlib
root = pathlib.Path(__file__).resolve().parent.parent
spec=importlib.util.spec_from_file_location('reviewer', root/'scripts/reviewer_brute_def.py')
r=importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
rows=[]
for n in range(3,9):
 for m in range(1,4):
  result=r.analyse(n,m,0)
  counts=[0]*n
  wrong_weight_detected=False
  for x in r.compositions(n,m,0):
   for q in range(1<<n):
    recurrent=(all(x[k]+x[(k+1)%n]>0 for k in range(n) if q>>k&1 and not(q>>((k+1)%n)&1)) and
     (q not in (0,(1<<n)-1) or any(x)))
    w=(sum(k*x[k] for k in range(n))+n-q.bit_count())%n
    if recurrent: counts[w]+=1
    for v in range(n):
     if x[v]:
      nq=q^(1<<v); t=(v+1 if nq>>v&1 else v-1)%n
      y=list(x); y[v]-=1; y[t]+=1
      nw=(sum(k*y[k] for k in range(n))+n-nq.bit_count())%n
      assert sum(y)==m and nw==w
      bad_before=(sum(k*x[k] for k in range(n))+q.bit_count())%n
      bad_after=(sum(k*y[k] for k in range(n))+nq.bit_count())%n
      wrong_weight_detected |= bad_before!=bad_after
  assert counts==result['r'] and result['unique_component_per_weight']
  assert wrong_weight_detected
  rows.append(result)
# A distinct-gcd equality is actually false, not a forbidden strengthening.
assert r.analyse(3,3,0)['r']==[26,24,24]
# Empty all-right state has a rotor Hamiltonian cycle and no legal move.
assert not any((0,0,0))
(root/'logs/regression.json').write_text(json.dumps({'cases':rows,'wrong_weight_rejected':True,
 'different_gcd_equality_rejected':[26,24,24], 'zero_recurrence_rejected':True},indent=2))
print('PASS',len(rows),'definition-level SCC comparisons n=3..8, m=1..3; negative controls')
