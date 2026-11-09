import itertools,json,pathlib,time,sys
D=pathlib.Path(__file__).resolve().parents[1]
n=int(sys.argv[1]);P=list(itertools.permutations(range(n)));ix={p:i for i,p in enumerate(P)};N=len(P)
mul=[[ix[tuple(p[q[i]] for i in range(n))] for q in P] for p in P]
# All subgroups by successive generator adjunction; explicit sets, no conjugacy pruning.
def gen(H,g):
 S=set(H);todo=list(H)
 while todo:
  h=todo.pop()
  for x in (g,):
   z=mul[h][x]
   if z not in S:S.add(z);todo.append(z)
  # Right generators of H are all its elements; safe but intentionally simple.
  for x in H:
   z=mul[h][x]
   if z not in S:S.add(z);todo.append(z)
 return frozenset(S)
groups=[frozenset([0])];seen=set(groups)
for H in groups:
 for g in range(N):
  if g in H:continue
  K=gen(H,g)
  if K not in seen:seen.add(K);groups.append(K)
 print('progress',n,len(groups),len(H),flush=True) if len(H)==N else None
print('groups',n,len(groups),flush=True)
# Restricted growth words enumerate each set partition once.
parts={}
def part(w):
 if len(w)==n:
  typ=tuple(sorted([w.count(c) for c in range(max(w)+1)],reverse=True))
  stab=sum(1<<j for j,p in enumerate(P) if all(w[i]==w[p[i]] for i in range(n)))
  parts.setdefault(typ,[]).append(stab);return
 for v in range(max(w)+2):part(w+[v])
part([0]);types=sorted(parts,reverse=True);rows=[]
for H in groups:
 mask=sum(1<<g for g in H);rows.append(sum(1<<i for i,t in enumerate(types) if any(mask&s==1 for s in parts[t])))
checks=[]
for i,t in enumerate(types):
 ids=[j for j,r in enumerate(rows) if r>>i&1];ideal=(1<<len(types))-1
 for j in ids:ideal&=rows[j]
 witnesses=[j for j in ids if rows[j]==ideal]
 checks.append(dict(partition=t,ideal=[types[k] for k in range(len(types)) if ideal>>k&1],witness_count=len(witnesses),witness_generating_elements=[P[g] for g in sorted(groups[witnesses[0]])] if witnesses else None))
 print(t,'witnesses',len(witnesses),'ideal',ideal,flush=True)
out=dict(n=n,permutations=N,subgroups=len(groups),set_partitions=sum(map(len,parts.values())),checks=checks)
(D/f'outputs/consumption{n}.json').write_text(json.dumps(out,indent=2)+'\n')
