import json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for n in range(4,9):
 full=(1<<n)-1;splits=[s for s in range(1,full) if s&1 and 2<=s.bit_count()<=n-2]
 adj=[]
 for s in splits:
  bits=0
  for j,t in enumerate(splits):
   if s!=t and any(v==0 for v in (s&t,s&(full^t),(full^s)&t,(full^s)&(full^t))):bits|=1<<j
  adj.append(bits)
 counts={};maxsize=[0]
 def rec(k,P,X):
  if P==0 and X==0:counts[k]=counts.get(k,0)+1;return
  union=P|X;u=(union&-union).bit_length()-1 if union else 0;todo=P&~adj[u]
  while todo:
   b=todo&-todo;i=b.bit_length()-1;rec(k+1,P&adj[i],X&adj[i]);P^=b;X|=b;todo^=b
 rec(0,(1<<len(splits))-1,0)
 r={'n':n,'nontrivial_splits':len(splits),'maximal_compatible_split_systems_by_size':counts,'max_top_cells':max(counts)+1,'top_cell_bound':n-2,'max_internal_codim1_faces':max(counts),'codim1_bound':n-3};print(r,flush=True);out.append(r)
(D/'outputs/rank2.json').write_text(json.dumps(out,indent=2))
