import itertools,json,pathlib
D=pathlib.Path(__file__).parent
# Exact source-proposed s=1,t=2 join(K2,2K2). Check literal N(v) minus N(S).
n=6;A={0,1};E={frozenset((0,1)),frozenset((2,3)),frozenset((4,5))}|{frozenset((a,b)) for a in A for b in range(2,6)}
def indep(s):return all(frozenset(p) not in E for p in itertools.combinations(s,2))
def subs(s):return [set(c) for k in range(len(s)+1) for c in itertools.combinations(sorted(s),k)]
def N(s):return {v for v in range(n) if any(frozenset((v,u)) in E for u in s)}
def alpha(s):return max(len(t) for t in subs(s) if indep(t))
fail=[]
for v in range(n):
 rest=set(range(n))-N({v})-{v}
 for s in subs(rest):
  if indep(s) and all(not indep(s|{u}) for u in rest-s):
   value=alpha(N({v})-N(s))
   if value!=1:fail.append({'v':v,'S':sorted(s),'alpha':value})
assert fail
out={'executed':True,'graph':'join(K2,2K2), source s=1 t=2','literal_neighborhood_condition_pass':False,'failures':fail,'conclusion':'Source proposed graph does not refute exact MathDB predicate by this check. Do not upgrade reported refutation to exact proof-body clearance.','schubert_n2':{'manual_defining_polynomials':{'12':'1','21':'x1'},'specialization_x1_1':[1,1],'k':2,'multi_layered_only':['12'],'all_maximizers_clause_false':True,'maximum_equality_false':False,'scope':'wording/strength discrepancy only; no credit'}}
(D/'bounded-checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
