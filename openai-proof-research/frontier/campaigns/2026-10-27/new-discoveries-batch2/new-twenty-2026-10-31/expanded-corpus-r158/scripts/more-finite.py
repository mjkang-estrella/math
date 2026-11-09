import itertools as I,json
# Exact (2,2) assignments: each edge chooses colour 0/1 and multiplicity 1/2.
for n in range(4,6):
 ae=list(I.combinations(range(n),2));cnt=0;tried=0
 for mask in range(1<<len(ae)):
  es=[e for j,e in enumerate(ae) if mask>>j&1]
  seen={0};q=[0]
  for u in q:
   for a,b in es:
    v=b if a==u else a if b==u else -1
    if v>=0 and v not in seen:seen.add(v);q.append(v)
  if len(seen)<n:continue
  cnt+=1
  for lab in I.product(range(4),repeat=len(es)):
   tried+=1;d=[[0]*n for _ in range(2)]
   for (u,v),s in zip(es,lab):c=s//2;w=1+s%2;d[c][u]+=w;d[c][v]+=w
   if all(d[s//2][u]!=d[s//2][v] for (u,v),s in zip(es,lab)):break
  else:raise AssertionError((n,es))
 print(json.dumps(dict(id=363188,n=n,graphs=cnt,assignments_tried=tried,failures=0)),flush=True)
# One representative of each 6-regular graph on 7,8,9 vertices.
for n,parts in [(7,[]),(8,[2,2,2,2]),(9,[9]),(9,[6,3]),(9,[5,4]),(9,[3,3,3])]:
 es=set(I.combinations(range(n),2));offset=0
 for s in parts:
  for j in range(s):es.discard(tuple(sorted((offset+j,offset+(j+1)%s))))
  offset+=s
 for p in I.permutations(range(1,n)):
  c=(0,)+p
  if all(tuple(sorted((c[i],c[(i+1)%n]))) in es for i in range(n)):break
 else:raise AssertionError((n,parts))
 print(json.dumps(dict(id=370093,n=n,complement_parts=parts,Hamiltonian_factor=list(c))),flush=True)
# All spanning edge subgraphs of Q3, coordinate colours.
n=8;es=[(u,u^(1<<i),i) for u in range(n) for i in range(3) if u<(u^(1<<i))]
tested=0
for mask in range(1<<len(es)):
 adj=[[] for _ in range(n)];m=0
 for j,(u,v,c) in enumerate(es):
  if mask>>j&1:adj[u].append((v,c));adj[v].append((u,c));m+=1
 d=2*m//n
 def path(u,vs,cs,left):
  if not left:return True
  return any(path(v,vs|{v},cs|{c},left-1) for v,c in adj[u] if v not in vs and c not in cs)
 assert any(path(u,{u},set(),d) for u in range(n));tested+=1
print(json.dumps(dict(id=382409,cube_dimension=3,subgraphs=tested,colouring='coordinate',failures=0)),flush=True)
