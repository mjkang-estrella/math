import pathlib,json,itertools,random
D=pathlib.Path(__file__).resolve().parents[1];out=[];rng=random.Random(107)
for q in [5,8,11,32]:
 def add(a,b):return a^b if q in [8,32] else (a+b)%q
 def mul(a,b):
  if q not in [8,32]:return a*b%q
  r=0
  while b:
   if b&1:r^=a
   b>>=1;a<<=1
   if a&q:a^={8:11,32:37}[q]
  return r
 def power(a,n):
  r=1
  while n:
   if n&1:r=mul(r,a)
   a=mul(a,a);n//=2
  return r
 def sub(a,b):return add(a,b) if q in [8,32] else (a-b)%q
 fs=set()
 for a in range(1,q):
  for b in range(q):
   ab=add(a,b)
   def m(x):return b if x==q else q if x==ab else add(b,mul(mul(a,a),power(sub(ab,x),q-2)))
   edges=tuple(sorted({tuple(sorted([x,m(x),m(m(x))])) for x in range(q+1)}));assert all(len(set(e))==3 for e in edges);fs.add(edges)
 fs=sorted(fs);n=q+1;pairs=list(itertools.combinations(range(1,len(fs)),2)) if q<32 else [tuple(rng.sample(range(1,len(fs)),2)) for _ in range(200)]
 failures=[];nodes=0
 for i,j in pairs:
  es=fs[0]+fs[i]+fs[j];adj=[[] for _ in range(2*n)]
  for a,e in enumerate(es):
   for v in e:adj[v].append(n+a);adj[n+a].append(v)
  calls=[0]
  def dfs(v,seen,length):
   calls[0]+=1
   if calls[0]>100000:return None
   if length==2*n:return 0 in adj[v]
   for w in sorted(adj[v],key=lambda w:sum(not(seen>>z&1) for z in adj[w])):
    if seen>>w&1:continue
    # do not close prematurely
    ans=dfs(w,seen|1<<w,length+1)
    if ans:return True
   return False
  ans=dfs(0,1,1);nodes+=calls[0]
  if not ans:failures.append({'i':i,'j':j,'DFS_calls':calls[0],'capped':calls[0]>100000})
 row={'q':q,'factor_count':len(fs),'triples_with_fixed_factor_tested':len(pairs),'Hamilton_cycles_found':len(pairs)-len(failures),'failed_or_capped':failures,'total_DFS_calls':nodes,'symmetry_scope':'fixed first factor; Fq factor transitivity from source affine conjugation; random 200 pairs for q32'};out.append(row);print(row,flush=True);(D/'outputs/hypergraphs.json').write_text(json.dumps(out,indent=2)+'\n')
