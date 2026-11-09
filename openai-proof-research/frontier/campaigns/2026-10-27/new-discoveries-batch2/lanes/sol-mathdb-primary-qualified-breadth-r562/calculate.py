import pathlib,json
P=pathlib.Path(__file__).parent
# Proposition 2.1 weighted Delannoy paths: H weight0, V weight current x, diagonal weight new x plus t.
N=12;F={};bad=[];slices=0
for m in range(N+1):
 for n in range(N+1):
  if not m or not n:F[m,n]={(0,0):1};continue
  d={}
  for src,shift,dt in [(F[m-1,n],0,0),(F[m,n-1],m,0),(F[m-1,n-1],m,1)]:
   for (q,t),v in src.items():d[q+shift,t+dt]=d.get((q+shift,t+dt),0)+v
  F[m,n]=d
  def uni(a):
   down=False
   for x,y in zip(a,a[1:]):
    if y<x:down=True
    if down and y>x:return False
   return True
  for q in range(m*n+1):
   a=[d.get((q,t),0) for t in range(min(m,n)+1)];slices+=1
   if not uni(a):bad.append({'m':m,'n':n,'q':q,'coefficients':a,'type':'t'})
  a=[sum(d.get((q,t),0) for t in range(min(m,n)+1)) for q in range(m*n+1)]
  if not uni(a):bad.append({'m':m,'n':n,'type':'specialization'})
# Exact identity check in Z[x], D=1-x-x²; -x/D²+1/D³=(1-x+x²+x³)/D³.
D=[1,-1,-1];num=[1,0,0,0]
for i,a in enumerate(D):num[i+1]-=a
out={'executed':True,'domain':'1<=m,n<=12','pairs':144,'t_slices':slices,'counterexamples':bad,'recurrence':'F(m,n)=F(m-1,n)+q^m F(m,n-1)+t q^m F(m-1,n-1)','sample_m1_n1':str(F[1,1]),'juggling_example37_numerator':num,'limits':'No all-parameter route follows from finite checks. Local proof algebra only for already-public Example3.7; no new result.'}
(P/'bounded-calculation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
