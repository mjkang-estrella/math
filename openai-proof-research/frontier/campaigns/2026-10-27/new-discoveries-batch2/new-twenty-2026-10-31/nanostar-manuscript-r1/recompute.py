"""Independent exact finite verification; standard library only, no discovery imports."""
from pathlib import Path
import json,hashlib,re,collections,math
B=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/nanostar-manuscript-r1')
A4=[3,167,334,19577,31657,39154,63314,702085,983055,1048576,1123336,1975461,2370559,2633948,3352289,3561823,4182461,4741118,5019445,5866457,8031112,8364922,11732914]
A3=[3,167,334,13107,16384,16449,19577,21932,31657,39154,63314]
A2=[3,256,376,384,564]
def factor(n):
 r=[];d=2
 while d*d<=n:
  e=0
  while n%d==0: n//=d;e+=1
  if e:r.append([d,e])
  d+=1
 if n>1:r.append([n,1])
 return r
def phi(n):
 v=n
 for p,e in factor(n):v=v//p*(p-1)
 return v
def model(k):
 g={0:set()}
 def child(u):
  v=len(g);g[v]={u};g[u].add(v);return v
 def arm(u,j):
  if j==0:return
  b=child(child(u));arm(child(b),j-1);arm(child(b),j-1)
 for _ in range(3):arm(child(0),k-1)
 return g
def code(g,v,p=None):return '('+''.join(sorted(code(g,w,v) for w in g[v] if w!=p))+')'
def dist(g,v):
 d={v:0};q=collections.deque([v])
 while q:
  u=q.popleft()
  for w in g[u]:
   if w not in d:d[w]=d[u]+1;q.append(w)
 return d
def check(A,k):
 V=set()
 for a in A:
  n=a;local=set()
  while n not in local:local.add(n);V.add(n);n=phi(n)
 assert 1 in V and all(n>0 and phi(n) in V for n in V)
 g={n:set() for n in V};E=set()
 for n in V:
  p=phi(n)
  if p!=n:g[n].add(p);g[p].add(n);E.add(tuple(sorted((n,p))))
 assert len(E)==len(V)-1
 ecc={n:max(dist(g,n).values()) for n in V};centre=min(ecc,key=ecc.get)
 assert sum(e==ecc[centre] for e in ecc.values())==1
 m=model(k);assert code(g,centre)==code(m,0)
 mapping={}
 def match(u,v,pu=None,pv=None):
  mapping[u]=v
  left=sorted((code(m,w,u),w) for w in m[u] if w!=pu)
  right=sorted((code(g,w,v),w) for w in g[v] if w!=pv)
  assert [x[0] for x in left]==[x[0] for x in right]
  for (_,w),(_,z) in zip(left,right):match(w,z,u,v)
 match(0,centre)
 assert len(set(mapping.values()))==len(V)==6*2**k-8
 assert {tuple(sorted((mapping[u],mapping[v]))) for u in m for v in m[u]}==E
 d=dist(g,centre);profile=[sum(x==j for x in d.values()) for j in range(max(d.values())+1)]
 rows=[{'label':n,'factorization':factor(n),'phi':phi(n),'parent':None if n==1 else phi(n),'layer':d[n]} for n in sorted(V)]
 for row in rows:assert math.prod(p**e for p,e in row['factorization'])==row['label']
 return {'stage':k,'generators':A,'order':len(V),'edges':len(E),'centre':centre,'layers':profile,'maximum_label':max(V),'rows':rows,'model_to_label':mapping,'canonical_tree':code(g,centre),'tree_isomorphism':'PASS'}
r={f'D{k}':check(A,k) for k,A in [(2,A2),(3,A3),(4,A4)]}
assert r['D2']['order']==16 and r['D2']['centre']==16 and r['D2']['layers']==[1,3,3,3,6]
assert r['D3']['order']==40
assert r['D4']['centre']==1024 and r['D4']['layers']==[1,3,3,3,6,6,6,12,12,12,24]
frozen=B/'frozen/expanded-corpus-r162';old=json.loads((frozen/'outputs/totient-stage4-certificate.json').read_text())
assert sorted(old['A'])==A4
for a,b in zip(old['vertices'],r['D4']['rows']):
 assert a['n']==b['label'] and a['factorization']==b['factorization'] and a['phi']==b['phi'] and a['parent']==b['parent']
assert len(old['vertices'])==r['D4']['order']
# Independently check the actual preorder labels in the formal certificate.
cert=(frozen/'lean/Certificate.lean').read_text();ls=re.search(r'def labels[^\n]*:=\s*!\[([^]]+)\]',cert)
if not ls:ls=re.search(r'def labels[^\n]*:=\s*#\[([^]]+)\]',cert)
assert ls,'labels parser failed'
labels=list(map(int,re.findall(r'\d+',ls.group(1))));assert len(labels)==88 and len(set(labels))==88
m=model(4)
# model's allocation is preorder, matching Tree.edges offsets.
assert set(labels)==set(x['label'] for x in r['D4']['rows'])
for i in m:
 for j in m:
  assert (j in m[i])==(i!=j and (phi(labels[i])==labels[j] or phi(labels[j])==labels[i]))
r['formal_label_adjacency']='PASS (all ordered pairs)'
r['phi_2_preimages']=[3,4,6];assert [phi(x) for x in [3,4,6]]==[2,2,2]
assert len(A4)==23 and len(A3)==11 and len(A2)==5
for k in range(1,8):
 assert len(model(k))==6*2**k-8
assert len([x for x in r['D4']['rows'] if x['layer']==10])==24
assert all(len(model(4)[i])==3 for i in model(4) if dist(model(4),0)[i] in [3,6,9])
r['order_recurrence_and_branch_layers']='PASS'
r['status']='PASS';r['input_certificate_discrepancies']=[]
(B/'recomputation.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({key:{s:r[key][s] for s in ['order','edges','centre','layers','maximum_label']} for key in ['D2','D3','D4']},indent=2));print(r['status'],r['formal_label_adjacency'])
