import pathlib,json,itertools
L=pathlib.Path(__file__).resolve().parents[1];vs=range(6);edges=list(itertools.combinations(vs,3));idx={e:i for i,e in enumerate(edges)};cl=[]
for q in itertools.combinations(vs,4):cl.append(sum(1<<idx[e] for e in itertools.combinations(q,3)))
def hit(cs,budget):
 if not cs:return True
 if budget==0:return False
 c=cs[0]
 while c:
  b=c&-c;c-=b
  if hit([x for x in cs[1:] if not x&b],budget-1):return True
 return False
checked=0;maxc=0;bad=[]
for es in itertools.combinations(range(20),11):
 h=sum(1<<e for e in es);cs=[c for c in cl if c&h==c];maxc=max(maxc,len(cs));checked+=1
 if not hit(cs,3):bad.append(list(es));print('CANDIDATE',bad[-1],flush=True)
r=dict(vertices=6,host_edges=11,hosts=checked,max_K4_copies=maxc,failures=bad,interpretation='Every checked host has a K4^(3)-free subhypergraph with at least 8 edges iff failures is empty. No multihypergraphs checked.');print(r,flush=True);(L/'host-results.json').write_text(json.dumps(r,indent=2))
