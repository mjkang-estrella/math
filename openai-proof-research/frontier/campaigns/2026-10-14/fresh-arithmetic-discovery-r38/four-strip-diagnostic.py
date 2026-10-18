#!/usr/bin/env python3
"""MIT. Finite test of an explicitly stated sufficient combinatorial lemma."""
import importlib.util,json,sys
from pathlib import Path
p=Path(__file__).parent
s=importlib.util.spec_from_file_location('q',p/'quotient-diagnostic.py');q=importlib.util.module_from_spec(s);s.loader.exec_module(q)
def count(lam,n):
 # lambda/nu is a union of at most four horizontal strips iff lambda_i >= nu_i >= lambda_(i+4).
 return sum(all((lam[i] if i<len(lam) else 0)>=(nu[i] if i<len(nu) else 0)>=(lam[i+4] if i+4<len(lam) else 0) for i in range(max(len(lam),len(nu)))) for nu in q.parts(n))
def main(top):
 rows=[]
 for m in range(3,top+1):
  n=m*(m+1)//2;small=(m-2)*(m-1)//2;rho=tuple(range(m,0,-1));bad=[];mins=None
  vals={lam:count(lam,small) for lam in q.parts(n)}
  for lam in q.parts(n):
   if lam in [(n,),(1,)*n]:continue
   tr=q.transpose(lam);k=max(q.kostka(lam,rho),q.kostka(tr,rho));c=max(vals[lam],vals[tr]);v=max(k,c)
   if v<m-1:bad.append({'lambda':lam,'K':k,'removals':c})
  rows.append({'m':m,'bad':bad});print(m,len(bad),bad[:6],file=sys.stderr)
 return rows
if __name__=='__main__':print(json.dumps(main(int(sys.argv[1]) if len(sys.argv)>1 else 7),indent=2))
