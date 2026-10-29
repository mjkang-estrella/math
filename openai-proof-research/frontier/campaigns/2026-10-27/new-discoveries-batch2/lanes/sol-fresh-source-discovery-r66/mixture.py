import runpy,pathlib,sys,json
from itertools import permutations,combinations
from fractions import Fraction as F
from math import prod
L=pathlib.Path(__file__).resolve().parent
sys.argv=['scan.py','--exact']; S=runpy.run_path(str(L/'scan.py'));parts=S['parts']
found=None;checks=0
for n in [3,4]:
 for d in range(3,13):
  shapes=list(parts(d,n));ms=[set(permutations(l)) for l in shapes]
  for t in [.1,.5,.9]:
   for x in [1.1,2.,10.,100.]:
    vd=[]
    for es in ms:
     vals=[];ders=[]
     for i in range(n+1):
      vals.append(sum(t**sum(j*v for j,v in enumerate(e))*x**sum(e[:i]) for e in es))
      ders.append(sum(sum(e[:i])*t**sum(j*v for j,v in enumerate(e))*x**sum(e[:i]) for e in es))
     vd.append((vals,ders))
    for a,b in combinations(range(len(shapes)),2):
     for w in [1e-6,.001,1.,1000.,1e6]:
      vs=[vd[a][0][i]+w*vd[b][0][i] for i in range(n+1)]
      ds=[vd[a][1][i]+w*vd[b][1][i] for i in range(n+1)]
      for i in range(1,n):
       D=2*ds[i]/vs[i]-ds[i-1]/vs[i-1]-ds[i+1]/vs[i+1];checks+=1
       if D<-1e-7:
        tf=F(str(t));xf=F(str(x));wf=F(str(w))
        def calc(es,i):
         V=sum(tf**sum(j*v for j,v in enumerate(e))*xf**sum(e[:i]) for e in es)
         D=sum(sum(e[:i])*tf**sum(j*v for j,v in enumerate(e))*xf**sum(e[:i]) for e in es)
         return V,D
        ab=[[calc(ms[k],j) for j in range(n+1)] for k in [a,b]]
        V=[ab[0][j][0]+wf*ab[1][j][0] for j in range(n+1)];D=[ab[0][j][1]+wf*ab[1][j][1] for j in range(n+1)]
        gap=2*D[i]/V[i]-D[i-1]/V[i-1]-D[i+1]/V[i+1];assert gap<0
        found={'n':n,'a':shapes[a],'b':shapes[b],'w':str(wf),'t':str(tf),'x':str(xf),'i':i,'gap':str(gap)};break
      if found:break
     if found:break
    if found:break
   if found:break
  if found:break
 if found:break
(L/'mixture.json').write_text(json.dumps({'checks':checks,'witness':found,'not_source_counterexample':True},indent=2));print((L/'mixture.json').read_text())
