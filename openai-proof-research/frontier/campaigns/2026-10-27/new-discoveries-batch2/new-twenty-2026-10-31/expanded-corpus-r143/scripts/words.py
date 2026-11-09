import json,random,time,sys
random.seed(143)
mode=sys.argv[1]
if mode=='pseudo':
 out=[]
 for b in range(55,71):
  for a in range(1,b):
   if b==2*a:continue
   target=4*b+100; nodes=[0]; budget=12000
   masks=[(1<<(2*p+1))-1 for p in range(target//3+1)]
   def dfs(w,n):
    nodes[0]+=1
    if n==target:return w
    if nodes[0]>budget:return None
    for c in (0,1):
     z=(w<<1)|c
     if n>=b and ((z>>b)&1)!=c and ((z>>(b-a))&1)!=((z>>b)&1):continue
     if any((z^(z>>p))&masks[p]==0 for p in range(1,n//3+1)):continue
     ans=dfs(z,n+1)
     if ans is not None:return ans
    return None
   z=dfs(0,1)
   r={'a':a,'b':b,'target':target,'nodes':nodes[0],'found':z is not None}
   if z is not None:r['word']=format(z,'0%db'%target)
   out.append(r)
  print(b,len(out),flush=True);json.dump(out,open('outputs/pseudo.json','w'))
elif mode=='steady':
 out=[]
 def good(w):
  if any(w[-2*p:-p]==w[-p:] for p in range(1,len(w)//2+1)):return False
  for j in range(len(w)-1):
   v=w[:j]+w[j+1:]
   if any(v[-2*p:-p]==v[-p:] for p in range(1,len(v)//2+1)):return False
  return True
 for case in range(120):
  n=40 if case<60 else 80; u=5+case%4
  lists=[random.sample(range(u),4) for _ in range(n)]; nodes=[0]
  def dfs(w):
   nodes[0]+=1
   if len(w)==n:return w
   if nodes[0]>3000:return None
   for c in lists[len(w)]:
    if good(w+[c]):
     z=dfs(w+[c])
     if z is not None:return z
   return None
  z=dfs([]);out.append({'case':case,'lists':lists,'nodes':nodes[0],'witness':z})
  json.dump(out,open('outputs/steady.json','w'))
 print('cases',len(out),'witnesses',sum(r['witness'] is not None for r in out),flush=True)
