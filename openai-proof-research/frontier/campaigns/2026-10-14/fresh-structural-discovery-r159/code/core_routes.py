from pathlib import Path
import json
ROOT=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r159')
def solve(p,q,max_states=200000):
 n=p+q;adj={v:range(p,n) if v<p else range(p) for v in range(n)}
 demands=[(i,i+1) for i in range(0,p,2)]+[(p+i,p+i+1) for i in range(0,q,2)]
 def paths(a,b):
  out=[]
  def dfs(path,mask):
   if path[-1]==b:out.append((mask,path));return
   if len(path)==n:return
   for w in adj[path[-1]]:
    if w in path:continue
    u=path[-1];l,r=(u,w) if u<p else (w,u);e=l*q+r-p
    dfs(path+[w],mask|(1<<e))
  dfs([a],0);return sorted(out,key=lambda z:len(z[1]))
 opts=[paths(*d) for d in demands]; count=0
 def search(k,mask,chosen):
  nonlocal count
  count+=1
  if count>max_states:raise RuntimeError('bounded search cap')
  if k==len(demands):return chosen
  for m,pa in opts[k]:
   if m&mask:continue
   sol=search(k+1,mask|m,chosen+[pa])
   if sol:return sol
  return None
 try:sol=search(0,0,[]);status='witness' if sol else 'exhausted-finite'
 except RuntimeError:sol=None;status='cap'
 return {'p':p,'q':q,'status':status,'states':count,'paths':sol,'options':[len(v) for v in opts]}
if __name__=='__main__':
 rows=[solve(2,2),solve(2,4),solve(4,4)]
 (ROOT/'receipts/core-routes.json').write_text(json.dumps(rows,indent=2)); print(json.dumps(rows,indent=2))
