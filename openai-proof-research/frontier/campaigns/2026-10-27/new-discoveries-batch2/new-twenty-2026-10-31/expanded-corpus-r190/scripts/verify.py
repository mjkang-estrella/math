import pathlib,json,collections
D=pathlib.Path(__file__).resolve().parents[1];a=json.loads((D/'outputs/flows.json').read_text());out=[];unique=set()
for x in a:
 n=x['n'];es=x['edges'];ls=x['labels'];deg=[sum(v in e for e in es) for v in range(n)];adj=[set() for _ in range(n)]
 for v,w in es:adj[v].add(w);adj[w].add(v)
 def conn(skip=None):
  seen={0};q=[0]
  for v in q:
   for w in adj[v]:
    if skip is not None and {v,w}==set(skip):continue
    if w not in seen:seen.add(w);q.append(w)
  return len(seen)==n
 valid=ls is not None and all(z in [-2,-1,1,2] for z in ls) and all(sum(z for e,z in zip(es,ls) if v in e)==0 for v in range(n));bridgeless=conn() and all(conn(e) for e in es);unique.add((n,tuple(map(tuple,es))))
 out.append({'n':n,'valid_labels':valid,'degree_five':deg==[5]*n,'two_edge_connected':bridgeless})
r={'sample_count':len(a),'distinct_labelled_graphs':len(unique),'valid':sum(z['valid_labels'] for z in out),'two_edge_connected':sum(z['two_edge_connected'] for z in out),'rows':out}
(D/'outputs/flow-verification.json').write_text(json.dumps(r,indent=2));print({k:v for k,v in r.items() if k!='rows'})
# Validate source Example 6.6 against the chosen modular convention.
A={0,3,4,5,6,8,9,10,11,13,14,15,16,18,19,21};N=25;p=5
free=all(not(set((a+j*d)%N for j in range(p))<=A) for a in range(N) for d in range(1,N) if len(set((a+j*d)%N for j in range(p)))==p)
cover={((a+4*d)%N) for a in range(N) for d in range(1,N) if a+3*d<N and all(a+j*d in A for j in range(4))}
s={'source_example_free':free,'source_example_covers':(A|cover)==set(range(N))};(D/'outputs/modular-sanity.json').write_text(json.dumps(s,indent=2));print(s)
