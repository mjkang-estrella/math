import pathlib,json,itertools,math
D=pathlib.Path(__file__).resolve().parents[1];out={}
p=5;S=(1,1,4,4);perms=sorted(set(itertools.permutations(S)));ps=[]
for seq in perms:
 total=0;sums=[]
 for x in seq:total=(total+x)%p;sums.append(total)
 ps.append({'sequence':seq,'partial_sums':sums,'distinct':len(set(sums))==len(sums)})
assert not any(x['distinct'] for x in ps)
out['329761']={'scope':'Literal signed multiset diagnostic only; excluded as formulation issue, not discovery','p':p,'multiset':S,'permutations':ps}
rows=[]
for t in range(2,41):
 phi=sum(math.gcd(t,a)==1 for a in range(1,t));nt=sum(math.gcd(t,a+b)==1 for a in range(1,t) for b in range(1,t));assert nt==(t-2)*phi
 for k in range(5):
  n=t*(k+1);count=sum(math.gcd(n,abs(a-c))==k+1 for a in range(1,n) for c in range(1,n));assert count==nt+t*phi*k
 rows.append({'t':t,'phi':phi,'nt':nt,'checked_k':list(range(5))})
out['339986']={'scope':'Source Theorem 10 diagnostic; no new result','rows':rows}
(D/'outputs/small.json').write_text(json.dumps(out,indent=2)+'\n');print('signed permutations',len(ps),'totient parameter pairs',39*5)
