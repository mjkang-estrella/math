from check import *

def main():
 records=[];blind=[];count=0
 for d in range(9,19):
  for p in itertools.product(range(1,d-1),repeat=3):
   if sum(p)!=d:continue
   for a in range(max(p),d-max(p)+1):
    if a==p[0]:continue
    s=(a,d-a);ts,A=matrix(s,p);count+=1
    n=len(A);v=sum(A[i][j]*A[j][i] for i in range(n) for j in range(n))
    if v==n:
     import sympy as S
     t=S.Symbol('t');poly=S.Matrix(A).charpoly(t).as_expr().factor()
     rec={'s':s,'p':p,'N':n,'tr2':v,'tr4':tr(mul(mul(A,A),mul(A,A))),'characteristic_polynomial':str(poly),'tables':ts,'matrix':A}
     blind.append(rec)
     if len(blind)>=3:break
   if len(blind)>=3:break
  records.append({'degree':d,'cumulative_pairs':count})
  if len(blind)>=3:break
 result={'status':'PASS','coverage':records,'second_moment_route_counterexamples':blind,'note':'counterexamples to a proposed sufficient proof invariant, not to the source conjecture'}
 (P/'moment-probe.json').write_text(json.dumps(result,indent=2));print(json.dumps({k:v for k,v in result.items() if k!='second_moment_route_counterexamples'},indent=2)); print([{k:v for k,v in x.items() if k not in ['tables','matrix']} for x in blind])
if __name__=='__main__':main()
