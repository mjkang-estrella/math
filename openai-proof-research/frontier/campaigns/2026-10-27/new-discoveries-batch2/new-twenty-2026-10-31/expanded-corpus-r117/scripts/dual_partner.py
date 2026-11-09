import pathlib,json,collections,time
D=pathlib.Path(__file__).resolve().parents[1]; ss=json.loads((D/'outputs/dual-follow.json').read_text());V=[(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1),(-1,0,0,0),(0,-1,0,0),(0,0,-1,0),(0,0,0,-1)]
def sub(a,b):return (a%8-b%8)%8+8*((a//8-b//8)%8)
DI=[[sub(a,b) for b in range(64)] for a in range(64)]
out=[];t=time.time()
for row in ss:
 if row['periods']:continue
 S=row['S']; target=[]
 for h in range(64):
  v=[sum(V[((h%8)*(x%8)+(h//8)*(x//8))%8][k] for x in S) for k in range(4)];target.append(sum(a*a for a in v)//8)
 cand=[x for x in range(1,64) if target[x]];nodes=[0];solutions=[]
 def rec(T,C,used):
  nodes[0]+=1
  if len(T)==8:solutions.append(T);return
  if len(T)+len(C)<8:return
  for i,x in enumerate(C):
   nu=used.copy();ok=True
   for y in T:
    for d in (DI[x][y],DI[y][x]):
     nu[d]+=1
     if nu[d]>target[d]:ok=False;break
    if not ok:break
   if ok:rec(T+[x],[z for z in C[i+1:] if target[DI[x][z]]],nu)
 rec([0],cand,[0]*64)
 r={'S':S,'support':len(cand),'nodes':nodes[0],'partners':solutions};out.append(r);print(r,flush=True)
(D/'outputs/dual-partners.json').write_text(json.dumps(out,indent=2));print('completed',len(out),'nodes',sum(x['nodes'] for x in out),'partners',sum(len(x['partners']) for x in out),'seconds',time.time()-t)
