import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for cyc in [0,1]:
 w=json.loads((D/f'outputs/replication-descent-{cyc}.json').read_text())['feasible_vectors'][-1];n=len(w);bad=[];hist={}
 for m in range(1,1<<n):
  k=m.bit_count();v=max([w[i] for i in range(n) if m>>i&1]+[w[i]+w[(i+1)%n] for i in range(n if cyc else n-1) if m>>i&1 and m>>((i+1)%n)&1]);hist[v-k]=hist.get(v-k,0)+1
  if v<k:bad.append(m)
 assert not bad
 out.append({'cycle':bool(cyc),'weights':w,'sum':sum(w),'subsets':(1<<n)-1,'bad_subsets':bad,'slack_histogram':hist})
(D/'outputs/replication-descent-exact.json').write_text(json.dumps(out,indent=2));print([(o['cycle'],o['sum'],len(o['bad_subsets'])) for o in out])
