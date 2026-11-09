import itertools,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for n in range(2,7):
 col=[1<<j for j in range(n)];square=[tuple(range(n))];count=0;bad=[];choices=list(itertools.combinations(range(n),2))
 rows=[[p for p in itertools.permutations(range(n)) if p[0]==r] for r in range(n)]
 def plex():
  cc=[0]*n;ss=[0]*n
  def go(r):
   if r==n:return True
   for a,b in choices:
    x,y=square[r][a],square[r][b]
    if cc[a]==2 or cc[b]==2 or ss[x]==2 or ss[y]==2:continue
    cc[a]+=1;cc[b]+=1;ss[x]+=1;ss[y]+=1
    if go(r+1):return True
    cc[a]-=1;cc[b]-=1;ss[x]-=1;ss[y]-=1
   return False
  return go(0)
 def gen(r):
  global count
  if r==n:
   count+=1
   if not plex():bad.append(list(square));print('FAIL',n,square,flush=True)
   return
  for p in rows[r]:
   if any(col[c]>>p[c]&1 for c in range(n)):continue
   for c in range(n):col[c]|=1<<p[c]
   square.append(p);gen(r+1);square.pop()
   for c in range(n):col[c]^=1<<p[c]
 gen(1);out.append(dict(n=n,reduced_squares=count,bad=bad));print(n,count,'failures',len(bad),flush=True)
(D/'outputs/latin6.json').write_text(json.dumps(out,indent=2))
