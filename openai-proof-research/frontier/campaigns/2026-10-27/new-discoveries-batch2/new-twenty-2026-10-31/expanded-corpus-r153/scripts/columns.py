import itertools,json,pathlib
L=pathlib.Path(__file__).resolve().parents[1]
def parts(n,lo=1):
 if n==0:yield ()
 for x in range(lo,n+1):
  for p in parts(n-x,x):yield (x,)+p
out=[]
for n in range(1,8):
 P=list(itertools.permutations(range(n)))
 for sizes in parts(n):
  blocks=[];pos=0
  for s in sizes:blocks.append(tuple(range(pos,pos+s)));pos+=s
  # f(sigma)=sgn(sigma)*2^e(sigma); generic coset exponents 3^rank
  keys={tuple(tuple(sorted(p[j] for j in b)) for b in blocks) for p in P};rank={k:i for i,k in enumerate(sorted(keys))}
  ex={p:3**rank[tuple(tuple(sorted(p[j] for j in b)) for b in blocks)] for p in P}
  actual=[]
  for i in range(n):
   for j in range(i+1,n):
    ratios={};ok=True
    for p in P:
     q=list(p);q[i],q[j]=q[j],q[i];d=ex[tuple(q)]-ex[p];pair=(p[i],p[j])
     if pair in ratios and ratios[pair]!=d:ok=False;break
     ratios[pair]=d
    if ok:
     # ratio must be a potential difference on the complete row graph
     z={0:0};z.update({a:ratios[(0,a)] for a in range(1,n)})
     ok=all(d==z[b]-z[a] for (a,b),d in ratios.items())
    if ok:actual.append([i,j])
  expected=[[i,j] for b in blocks for i,j in itertools.combinations(b,2)]
  out.append({'n':n,'sizes':sizes,'cosets':len(keys),'permutations':len(P),'pairs':actual,'expected':expected,'match':actual==sorted(expected),'excluded_partition':len(sizes)==2 and sizes[0]==1})
 print(n,'done',flush=True)
(L/'outputs/columns.json').write_text(json.dumps(out,indent=2));print('tested',len(out),'nonexcluded failures',sum(not r['match'] and not r['excluded_partition'] for r in out))
