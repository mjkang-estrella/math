import pathlib,json,math
from check import compressed,literal,add,mul,shape
b=pathlib.Path(__file__).resolve().parent
# independent direct subset enumeration of the 16-vertex whole-class obstruction
n=847;vs=[v for v in range(1,n) if math.gcd(v,n) in (77,121)]
a=[0]*17
for mask in range(1<<len(vs)):
 z=[vs[i] for i in range(len(vs)) if mask>>i&1]
 if all(x*y%n for i,x in enumerate(z) for y in z[i+1:]):a[len(z)]+=1
while a[-1]==0:a.pop()
expected=[math.comb(6,k) for k in range(7)];expected[1]+=10
assert len(vs)==16 and a==expected and a[1]>a[2]<a[3]
# Published p^2 q formula independently matches class recurrence including source example.
comparisons=[]
for p,q in [(2,3),(3,5),(5,3),(11,7),(7,11)]:
 A=p*(q-1);B=(p-1)*(p+q-1);C=(p-1)*(q-1);D=p*(p-1)
 rhs=add(add([math.comb(A,k) for k in range(A+1)],[math.comb(B,k) for k in range(B+1)]),[-math.comb(C,k) for k in range(C+1)])
 rhs=add(rhs,[0]+[(p-1)*math.comb(D,k) for k in range(D+1)])
 got,ds,w,_=compressed(p*p*q);assert got==rhs
 comparisons.append({'p':p,'q':q,'degree':len(got)-1,'unimodal':not shape(got)[0],'log_concave':not shape(got)[1]})
# Check local literal source data independently, without gcd compression.
assert literal(45)==compressed(45)[0]
# Ultra-logconcavity stronger than source fails for actual n=16.
p=compressed(16)[0];d=len(p)-1
ulc=[i for i in range(1,d) if p[i]**2*math.comb(d,i-1)*math.comb(d,i+1)<p[i-1]*p[i+1]*math.comb(d,i)**2]
assert ulc and not shape(p)[1]
# Check extension-moment identity in H using explicit independent sets.
rows=[]
for k in range(5):
 sk=sa=sb=0
 for mask in range(1<<len(vs)):
  if mask.bit_count()!=k:continue
  z=[vs[i] for i in range(len(vs)) if mask>>i&1]
  if any(x*y%n==0 for i,x in enumerate(z) for y in z[i+1:]):continue
  av=[v for i,v in enumerate(vs) if not(mask>>i&1) and all(v*x%n for x in z)]
  A=len(av);edges=sum(x*y%n==0 for i,x in enumerate(av) for y in av[i+1:]);sk+=1;sa+=A;sb+=A*(A-1)-2*edges
 assert sk==a[k] and sa==(k+1)*a[k+1] and sb==(k+1)*(k+2)*a[k+2]
 rows.append({'k':k,'s_k':sk,'sum_available':sa,'sum_ordered_independent_extension_pairs':sb})
out={'whole_class_obstruction':{'n':n,'gcd_classes':[77,121],'vertices':vs,'polynomial':a,'strict_valley':[a[1],a[2],a[3]],'scope':'induced subgraph only; full n847 polynomial is log-concave'},'published_formula_comparisons':comparisons,'actual_n16_ulc_failure':{'polynomial':p,'failed_ranks':ulc},'extension_moment_checks':rows,'literal_n45_mass':sum(literal(45))}
(b/'routes.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
