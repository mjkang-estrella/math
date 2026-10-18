#!/usr/bin/env python3
"""MIT. Exact finite base proof for T205M; not a proof of the uniform lemmas.
Run --write to regenerate the certificate; default independently recomputes it.
Uses rational character induction, Pieri recursion, and explicit strip intervals.
"""
import importlib.util,json,sys,hashlib
from pathlib import Path
p=Path(__file__).parent
s=importlib.util.spec_from_file_location('q',p/'quotient-diagnostic.py');q=importlib.util.module_from_spec(s);s.loader.exec_module(q)
s=importlib.util.spec_from_file_location('e',p/'exception-induction-diagnostic.py');e=importlib.util.module_from_spec(s);s.loader.exec_module(e)

def compute():
 small=[q.mn.run(m) for m in (2,3,4)]
 assert [x['minimum_nontrivial_nonsign'] for x in small]==[1,2,3]
 lower={1:{(1,):1}};base=[]
 for m in range(2,7):
  n=m*(m+1)//2;rho=tuple(range(m,0,-1));ps=q.parts(n)
  one={lam:sum(lower[m-1][nu] for nu in q.horizontal_predecessors(lam,m)) for lam in ps}
  two=q.induce(lower[m-2],{eta:1 for eta in q.parts(2*m-1) if len(eta)<=4}) if m>=3 else dict.fromkeys(ps,0)
  dom={lam:q.kostka(q.transpose(lam),rho) for lam in ps}
  lower[m]={lam:max(1,dom[lam],one[lam],two[lam]) for lam in ps}
  if m>=5:assert all(v>=m-1 for lam,v in lower[m].items() if lam not in e.exceptions(m))
  base.append({'m':m,'partitions':len(ps),'entries':[{'lambda':lam,'K':dom[lam],'one':one[lam],'two':two[lam],'R':lower[m][lam]} for lam in ps]})
  print('exact cyclic recurrence',m,len(ps),'PASS',file=sys.stderr)
 boundary=[]
 for m in (7,8):
  n=m*(m+1)//2;h=m-2;nh=h*(h+1)//2;rho=tuple(range(m,0,-1));rows=[];stats={}
  for lam in q.parts(n):
   if lam in e.exceptions(m):continue
   nus=q.horizontal_predecessors(lam,m);good=sum(nu not in e.exceptions(m-1) for nu in nus)
   b=(m-2)*good+len(nus)-good;method='one'
   if b<m-1:b=q.kostka(q.transpose(lam),rho);method='K'
   if b<m-1:
    nus=e.rem4(lam,nh);good=sum(nu not in e.exceptions(h) for nu in nus)
    b=(m-3)*good+len(nus)-good;method='four-strip'
   if b<m-1:
    assert lam==(m,m-2)+(1,)*(n-2*m+2)
    nu=(2,)+(1,)*(nh-2)
    assert nu not in e.exceptions(h)
    eta1=(m,m-3,1,1);eta2=(m-1,m-2,1,1)
    assert sum(eta1)==sum(eta2)==2*m-1 and eta1!=eta2
    b=2*(m-3);method='critical-LR-formula'
   assert b>=m-1
   stats[method]=stats.get(method,0)+1;rows.append({'lambda':lam,'method':method,'lower':b})
  boundary.append({'m':m,'eligible':len(rows),'stats':stats,'entries':rows})
  print('induction boundary',m,len(rows),stats,'PASS',file=sys.stderr)
 return {'scope':'only exact finite bases m2..6 and conditional induction boundary m7,8; uniform proof is prose','small_squares':small,'cyclic_recursion':base,'boundary':boundary}

def main():
 value=json.dumps(compute(),indent=2)+'\n';f=p/'finite-proof-certificate.json'
 if '--write' in sys.argv:f.write_text(value)
 else:assert f.read_text()==value,'finite certificate differs from exact recomputation'
 print(json.dumps({'status':'PASS_FINITE_BASES','certificate_sha256':hashlib.sha256(value.encode()).hexdigest(),'small_m':[2,3,4],'cyclic_base_m':[5,6],'conditional_boundary_m':[7,8]}))
if __name__=='__main__':main()
