import itertools,json,pathlib,time
L=pathlib.Path(__file__).resolve().parent
V=list(itertools.combinations(range(6),2));adj={a:{b for b in V if len(set(a)&set(b))==1} for a in V};C={(0,1),(0,2),(1,2)};S=set.union(*(adj[a] for a in C))-C;rest=set(V)-S;components=[]
while rest:
 todo=[rest.pop()];c=set(todo)
 while todo:
  for b in adj[todo.pop()]&rest:rest.remove(b);c.add(b);todo.append(b)
 components.append(len(c))
assert all(len(x)==8 for x in adj.values()) and len(S)==9 and sorted(components)==[3,3]
assert all(len(adj[a]&adj[b])==(4 if b in adj[a] else 4) for a,b in itertools.combinations(V,2))
out={'Brouwer_T6':{'vertices':15,'k':8,'lambda':4,'mu':4,'cut_size':9,'claimed_lower_bound':10,'component_sizes':components,'result':'known published counterexample reproduced; no new credit'}}
K=10;N=1<<K;div=[set() for i in range(N)]
def mul(a,b):
 r=0
 while b:
  if b&1:r|=a
  a<<=1;b>>=1
 return r
pairs=0
for a in range(1,N):
 for b in range(1,1<<(K-a.bit_length()+1)):
  n=mul(a,b);div[n].add(a);pairs+=1
checks=[]
for k in range(2,K+1):
 vals={n:len(div[n]) for n in range(1<<(k-1),1<<k)};mx=max(vals.values());wins=[n for n,d in vals.items() if d==mx];odd={n:d for n,d in vals.items() if n&1};om=max(odd.values());ow=[n for n,d in odd.items() if d==om];levels=sorted(set(odd.values()),reverse=True);runner=[n for n,d in odd.items() if len(levels)>1 and d==levels[1]]
 checks.append({'k':k,'max':mx,'winners':wins,'odd_winners':ow,'odd_second':runner});assert (1<<k)-2 in wins and ow==[(1<<k)-1]
 if k>=3 and k!=5:assert (1<<k)-3 in runner and (1<<k)-(1<<(k-2))-1 in runner
out['dismal_binary']={'k_range':[2,K],'ordered_factor_pairs':pairs,'checks':checks,'result':'no counterexample in finite range; does not prove either all-k statement; k=1 parked as domain edge, not credit'}
(L/'bounded-checks.json').write_text(json.dumps(out,indent=2)+'\n');print('Known T6 witness and binary dismal k=2..10 PASS; factor pairs',pairs)
