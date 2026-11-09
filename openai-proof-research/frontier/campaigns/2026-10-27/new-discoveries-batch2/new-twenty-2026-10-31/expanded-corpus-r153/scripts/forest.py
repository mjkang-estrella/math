import itertools,json,pathlib,time
L=pathlib.Path(__file__).resolve().parents[1];n=6;r=3;k=4
E=list(itertools.combinations(range(n),r)); index={e:i for i,e in enumerate(E)}
F=set()
for p in itertools.permutations(range(n)):
 F.add(sum(1<<index[tuple(sorted(p[j:j+r]))] for j in range(k)))
bad=bytearray(1<<len(E))
for m in F:bad[m]=1
for i in range(len(E)):
 bit=1<<i
 for base in range(0,len(bad),2*bit):
  for j in range(bit):
   if bad[base+j]:bad[base+bit+j]=1
best=-1;w=[];cnt=0;hist={}
for m,b in enumerate(bad):
 if not b:
  cnt+=1;c=m.bit_count();hist[c]=hist.get(c,0)+1
  if c>best:best=c;w=[m]
  elif c==best:w.append(m)
out={'n':n,'r':r,'k':k,'hypergraphs':len(bad),'distinct_forbidden_path_masks':len(F),'path_free':cnt,'histogram':hist,'maximum':best,'maximizers':len(w),'example_edges':[E[i] for i in range(len(E)) if w[0]>>i&1],'conjectured':10,'scope':'At n=6 four-edge tight forest can only be a single tight path; multiple nontrivial components require at least eight vertices.'}
(L/'outputs/forest.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
