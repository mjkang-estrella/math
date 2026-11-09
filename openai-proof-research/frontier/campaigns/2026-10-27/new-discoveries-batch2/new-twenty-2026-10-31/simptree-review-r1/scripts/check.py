import itertools as it,json,pathlib,collections,hashlib
L=pathlib.Path(__file__).resolve().parents[1]
F=[frozenset(int(c,16) for c in s) for s in ['0123','1234','1235','1356','1456','1457','0147','0467','89AB']]
def faces(F,k):return sorted({tuple(x) for f in F for x in it.combinations(sorted(f),k+1)})
def stats(F):return [len(faces(F,k)) for k in range(len(next(iter(F))))]
result={'facets':[sorted(f) for f in F],'f_vector':stats(F),'circuits':{}}
# Simple cycles in bipartite face/facet incidence graph. Root at smallest face;
# reject reversal by first facet < last facet. Every circuit occurs exactly once.
for m in range(3):
 S=[frozenset(x) for x in faces(F,m)]; inc=[[i for i,f in enumerate(F) if s<=f] for s in S]; fi=[[j for j,s in enumerate(S) if s<=f] for f in F]
 counts=collections.Counter(); v1=collections.Counter(); v23=collections.Counter(); witnesses={}; digest=hashlib.sha256()
 def record(ss,ff):
  r=len(ff);counts[r]+=1;digest.update((str((ss,ff))+'\n').encode())
  for version,C in [('v1',v1),('v2_v3',v23)]:
   good=False
   if r>=3:
    for a in range(r):
     # rotate cycle to root at ss[a], traversing ff[a], ...
     ts=ss[a:]+ss[:a]; tf=ff[a:]+ff[:a]
     missing=[not S[ts[0]]<=F[f] for f in tf[1:-1]]
     if not (all(missing) if version=='v1' else any(missing)):continue
     options=[]
     for z in range(1,r):
      common=F[tf[z-1]]&F[tf[z]]
      options.append([frozenset(x) for x in it.combinations(sorted(common),3) if S[ts[z]]<=frozenset(x)])
     if version=='v1':
      def sdr(j,used):
       return j==len(options) or any(t not in used and sdr(j+1,used|{t}) for t in options[j])
      good=sdr(0,set())
     else:good=all(options)
     if good:
      witnesses.setdefault(version,{'faces':[sorted(S[s]) for s in ts],'facet_indices':tf});break
   if good:C[r]+=1
 def dfs(root,ss,ff,usedS,usedF):
  for f in inc[ss[-1]]:
   if f in usedF:continue
   if root in fi[f] and len(ff)>=1 and ff[0]<f:record(ss,ff+[f])
   for s in fi[f]:
    if s>root and s not in usedS:dfs(root,ss+[s],ff+[f],usedS|{s},usedF|{f})
 for root in range(len(S)):dfs(root,[root],[],{root},set())
 result['circuits'][m]={'by_length':dict(counts),'v1_cycles_up_to_rotation_reversal':dict(v1),'v2_v3_cycles_up_to_rotation_reversal':dict(v23),'witnesses':witnesses,'enumeration_sha256':digest.hexdigest()}
 print('finished m',m,dict(counts),flush=True)
result['later_shared_triangles']=[[list(t) for t in faces([F[i]&F[j] for j in range(i+1,len(F))],2)] if i+1<len(F) else [] for i in range(len(F))]
# Complete ordering dynamic programming: attachment must be a full triangle,
# including all shared vertices; memo records every reachable prefix subset.
reachable={0}
for mask in range(1<<len(F)):
 if mask not in reachable:continue
 for i,f in enumerate(F):
  if mask>>i&1:continue
  prior=[F[j] for j in range(len(F)) if mask>>j&1]
  attachment=[s for k in range(4) for s in faces([f],k) if any(set(s)<=g for g in prior)]
  maxima=[set(s) for s in attachment if not any(set(s)<set(t) for t in attachment)]
  if not prior or len(maxima)==1 and len(maxima[0])==3:reachable.add(mask|1<<i)
result['complete_order_exists']=(1<<len(F))-1 in reachable
result['reachable_prefixes']=len(reachable)
# Exact source subconstruction: coned core of printed Figure 3 (v1/v3).
core=[frozenset(x) for x in [(1,2,3),(2,3,4),(3,4,5),(1,4,5)]]
mp={1:6,2:5,3:1,4:7,5:0}
coned=[frozenset(mp[v] for v in f)|{4} for f in core]
assert coned==F[4:8]
build=coned[:]; steps=[]
for i in [3,2,1,0,8]:
 old=set().union(*build);build.append(F[i]);steps.append({'add_facet':i,'new_vertices':sorted(F[i]-old),'f_vector':stats(build)})
result['printed_core_augmentation']={'vertex_map':mp,'cone_vertex':4,'initial_f_vector':stats(coned),'steps':steps}
# Small exhaustive connected screen (all nonempty families on p<=5 in d=2,
# p<=6 in d=3): top count required; tree = complete facet ordering.
def has_order(G):
 R={0};N=len(G)
 for mask in range(1<<N):
  if mask not in R:continue
  old=[G[j] for j in range(N) if mask>>j&1];U=set().union(*old) if old else set()
  for i,f in enumerate(G):
   if mask>>i&1:continue
   common=f&U
   if not old or len(common)==len(f)-1 and any(common<=g for g in old):R.add(mask|1<<i)
 return (1<<N)-1 in R
def connected(G,d):
 seen={0}
 while True:
  nxt=seen|{j for i in seen for j in range(len(G)) if len(G[i]&G[j])==d}
  if nxt==seen:return len(seen)==len(G)
  seen=nxt
screen=[]
for d,maxp in [(2,5),(3,6)]:
 for p in range(d+1,maxp+1):
  top=[frozenset(x) for x in it.combinations(range(p),d+1)];checked=hit=bad=0
  for G in it.combinations(top,p-d):
   if len(set().union(*G))!=p:continue
   checked+=1
   if not connected(G,d):continue
   vec=stats(G)
   if not any(vec[k]==(p-d)*__import__('math').comb(d,k)+__import__('math').comb(d,k+1) for k in range(1,d)):continue
   hit+=1;bad+=not has_order(G)
  screen.append({'dimension':d,'p':p,'top_count_full_support_families':checked,'connected_intermediate_count_matches':hit,'without_complete_order':bad})
result['small_screen']=screen
(L/'evidence/math.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
