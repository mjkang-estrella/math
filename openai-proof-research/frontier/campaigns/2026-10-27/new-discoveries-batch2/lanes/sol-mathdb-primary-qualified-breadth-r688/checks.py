import pathlib,json,hashlib,collections,math,re
O=pathlib.Path(__file__).resolve().parent
s=(O/'cayley-p23.txt').read_text()
for pat in ['Cayley','3n','8n','conjectur']:
 for m in list(re.finditer(pat,s,re.I))[:1]:print('cayley bounded',pat,s[max(0,m.start()-180):m.end()+750])
# Exact rational/integer integral via integration by parts: A(n,k)=sum n!/j!*(k-1)^j.
integ=[{'n':n,'k':k,'value':sum(math.factorial(n)//math.factorial(j)*(k-1)**j for j in range(n+1))} for n,k in [(0,-1),(1,-1),(2,-1),(3,-1)]]
# Directed Cayley BFS; permutation tuples; left shift positions and swap first two.
bfs=[]
for n in range(2,9):
 e=tuple(range(n));dist={e:0};q=collections.deque([e])
 while q:
  p=q.popleft()
  for t in [p[1:]+p[:1],(p[1],p[0])+p[2:]]:
   if t not in dist:dist[t]=dist[p]+1;q.append(t)
 assert len(dist)==math.factorial(n)
 d=max(dist.values());formula=(3*n*n-8*n+(9 if n%2 else 12))//4
 bfs.append({'n':n,'vertices':len(dist),'diameter':d,'claimed_formula':formula,'matches':d==formula})
print('executed integral',integ);print('executed BFS',bfs)
(O/'bounded-checks.json').write_text(json.dumps({'integral':{'method':'exact integration-by-parts polynomial','results':integ,'limit':'negative counts obstruct unsigned interpretation only; not a discovery'},'directed_cayley':{'method':'exact BFS for left rotation and first-position swap','results':bfs,'limit':'parameter instances only; no all-n proof or novelty'}},indent=2)+'\n')
