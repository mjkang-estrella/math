from check import *
def halfnonneg(p):
 if p.is_zero:return True
 # Leading sign at negative infinity, and every open-negative real root has even multiplicity.
 if p.LC()*(-1)**p.degree()<0:return False
 return all(m%2==0 or q.count_roots(-s.oo,0)==0 for q,m in p.sqf_list()[1])
cases=0;fails=[];identities=0
for lam in shapes:
 F=[poly(dp(lam[:i])) for i in range(len(lam)+1)];a=[]
 while any(not f.is_zero for f in F):
  a.append(F[-1]);G=[];running=s.Poly(0,x)
  for f in F:G.append(running);running+=f
  F=G
 for k in range(len(a)-2):
  D=a[k+1]**2-a[k]*a[k+2];cases+=1
  if not halfnonneg(D):
   fails.append({'lambda':lam,'k':k,'D':str(D.as_expr()),'at_minus_one':str(D.eval(-1))})
 for k in range(len(a)-3):
  A,B,C,D=a[k:k+4]
  assert (B+x*C)**2-(A+x*B)*(C+x*D)==B**2-A*C+x*(B*C-A*D)+x**2*(C**2-B*D)
  identities+=1
(P/'turan.json').write_text(json.dumps({'cases':cases,'failed':len(fails),'update_identities':identities,'first_failures':fails[:12],'status':'finite diagnostics, not proof'},indent=2)+'\n');print('TURAN',cases,len(fails),fails[:2], 'identities',identities)
