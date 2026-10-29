import itertools,json,pathlib
P=pathlib.Path(__file__).resolve().parent
m=5;r=4
support=[{0,4,5},{0,3,5},{0,4,5},{0,1,5}]
terms={d:[] for d in range(4,21,4)}
for ds in itertools.product(*[sorted(s) for s in support]):
 if sum(ds) in terms and all(ds[j]%4 != (ds[0]+j)%4 for j in range(1,4)):
  terms[sum(ds)].append(ds)
coeff={d:len(v)%2 for d,v in terms.items()}
rows=[]
for initial in itertools.product(range(2),repeat=5):
 q=list(initial)
 for n in range(5,1000): q.append(sum(q[n-j] for j in support[n%4] if j>0)%2)
 bad=[n for n in range(20,1000) if q[n] != sum(coeff[d]*q[n-d] for d in coeff)%2]
 if bad:
  n=bad[0];period=next(t for t in range(4,990,4) if q[t:t+5]==list(initial))
  rows.append({'initial':initial,'first_failure':n,'lhs':q[n],'rhs':sum(coeff[d]*q[n-d] for d in coeff)%2,'q_prefix':q[:n+1],'lag_values':{d:q[n-d] for d in coeff},'period':period})
  break
assert rows
# independently multiply the polynomial matrix det over F2 by permutation expansion
# row i, column (i-j)%4 gets coefficient x^j; j=0 represents -1=1.
det=[0]*21
for perm in itertools.permutations(range(4)):
 for ds in itertools.product(*[sorted(s) for s in support]):
  if all((i-ds[i])%4==perm[i] for i in range(4)):
   det[sum(ds)]^=1
assert any(coeff[d]!=det[d] for d in coeff)
# independent exact source counting diagnostic, no extra outcome
triples=list(itertools.product(range(7),repeat=3));triples=[t for t in triples if sum(t)==9]
allowed=[t for t in triples if t[1]%3 != (t[0]+1)%3 and t[2]%3 != (t[0]+2)%3]
distinct=[t for t in triples if len(set(t))==3]
same=[t for t in distinct if len({x%3 for x in t})==1]
assert 2*len(allowed)==2*len(triples)-len(distinct)+len(same)
out={'r':r,'m':m,'nonzero_coefficients':[[j for j in sorted(s) if j] for s in support],'source_terms':terms,'source_counts':{d:len(v) for d,v in terms.items()},'source_coefficient_parities':coeff,'actual_determinant_parities':{d:det[d] for d in range(0,21,4)},'witness':rows[0],'aux_conjecture2':{'m':6,'d':9,'total':len(triples),'distinct':len(distinct),'same_residue_distinct':len(same),'actual':len(allowed),'claimed':len(triples)-len(distinct)//2}}
(P/'checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
# Independent integer replay: signs change magnitudes but not the odd residual.
q=[0,0,0,0,1]
for n in range(5,23):q.append(sum(q[n-j] for j in support[n%4] if j>0))
possible=[range(-len(terms[d]),len(terms[d])+1,2) for d in terms]
residuals=[q[22]-sum(a*q[22-d] for a,d in zip(aa,terms)) for aa in itertools.product(*possible)]
assert all(z%2==1 for z in residuals)
assert len(residuals)==720
out['integer_replay']={'q0_through_q22':q,'coefficient_value_combinations':len(residuals),'all_residuals_odd':True,'min_residual':min(residuals),'max_residual':max(residuals)}
(P/'checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out['integer_replay']))
