import json,pathlib,time,math
D=pathlib.Path(__file__).resolve().parents[1];start=time.monotonic();out=[]
def factors(m):
 r=[];p=2
 while p*p<=m:
  if m%p==0:
   r.append(p)
   while m%p==0:m//=p
  p+=1
 if m>1:r.append(m)
 return r
for s in range(31,61):
 for a in range(1,(s+1)//2):
  b=s-a
  for m in range(2*s+1,5001,s):
   if max(factors(m))>b:continue
   M=list(range(-a,0))+list(range(1,b+1));blocks={}
   for t in range(1,m):
    residues={(x*t)%m for x in M}
    if 0 not in residues and len(residues)==s:blocks.setdefault(sum(1<<(x-1) for x in residues),t)
   target=(1<<(m-1))-1;forced=sum(1<<(x%m-1) for x in M)
   # The block covering 1 uses a unit splitter. Multiplying all splitters
   # by its inverse normalizes this unit to 1; hence this forced block loses none.
   opts=[[] for _ in range(m-1)]
   for mask,t in blocks.items():
    if mask&forced:continue
    z=mask
    while z:
     bit=z&-z;opts[bit.bit_length()-1].append((mask,t));z-=bit
   nodes=0;aborted=False
   def dfs(used,path):
    global nodes,aborted
    nodes+=1
    if nodes>50000:aborted=True;return None
    if used==target:return path
    remain=target^used;best=None
    while remain:
     bit=remain&-remain;remain-=bit
     poss=[(mask,t) for mask,t in opts[bit.bit_length()-1] if not mask&used]
     if not poss:return None
     if best is None or len(poss)<len(best):best=poss
     if len(best)==1:break
    for mask,t in best:
     r=dfs(used|mask,path+[t])
     if r:return r
     if aborted:return None
   r=dfs(forced,[1]);out.append({'k1':a,'k2':b,'m':m,'blocks':len(blocks),'nodes':nodes,'status':'witness' if r else 'node_cap' if aborted else 'unsat','splitter':r})
   if r:print('WITNESS',out[-1],flush=True)
   if time.monotonic()-start>105:break
  if time.monotonic()-start>105:break
 if time.monotonic()-start>105:break
(D/'splitter-extended-search.json').write_text(json.dumps(out,indent=2)+'\n')
print('instances',len(out),'nodes',sum(x['nodes'] for x in out),'capped',sum(x['status']=='node_cap' for x in out),'wall',time.monotonic()-start,'last',out[-1],flush=True)
