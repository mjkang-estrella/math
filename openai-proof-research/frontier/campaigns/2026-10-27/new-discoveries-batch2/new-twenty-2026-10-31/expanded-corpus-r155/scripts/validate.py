import json,pathlib,itertools,hashlib
L=pathlib.Path(__file__).resolve().parents[1];report={}
for m in [5,7,9,11]:
 r=json.loads((L/f'outputs/flower{m}.json').read_text());E=r['edges'];n=4*m;c=r['answer']['flow'];a,b=r['answer']['pair'];inc=[[] for _ in range(n)]
 for j,(u,v) in enumerate(E):inc[u].append(j);inc[v].append(j)
 assert all(len(es)==3 for es in inc)
 assert all(c[es[0]]^c[es[1]]^c[es[2]]==0 for es in inc)
 assert all(1<=v<=7 for v in c) and a!=b and a and b
 assert all(sum(c[e] in [a,b] for e in es)<=1 for es in inc)
 A={u for j,e in enumerate(E) if c[j]==a for u in e};B={u for j,e in enumerate(E) if c[j]==b for u in e}
 assert all(not((u in A and v in B) or (u in B and v in A)) for u,v in E)
 def connected(removed):
  adj=[[] for _ in range(n)]
  for j,(u,v) in enumerate(E):
   if j not in removed:adj[u].append(v);adj[v].append(u)
  seen={0};todo=[0]
  while todo:
   for v in adj[todo.pop()]:
    if v not in seen:seen.add(v);todo.append(v)
  return len(seen)==n
 assert all(connected(set(es)) for k in range(3) for es in itertools.combinations(range(len(E)),k))
 report[f'flower{m}']={'flow_and_pair_valid':True,'three_edge_connected':True,'search_nodes':r['search_nodes'],'complete_flows':r['complete_flows_examined']}
# Coverage of interrupted prefix is supported by flushed progress records.
prefix=[json.loads(s)['completed'] for s in (L/'outputs/bent14cubic-optimized.log').read_text().splitlines() if 'completed' in s]
assert max(prefix)==32000000
lo=32000000
for start in [32000000,40000000,48000000,56000000,64000000]:
 r=json.loads((L/f'outputs/bent14-{start}.log').read_text().splitlines()[-1]);assert r['start']==lo and not r['found'];lo=r['stop']
assert lo==2**26
report['bent14']={'completed_gray_indices':[0,lo],'found':0,'prefix_evidence':'flushed million-case progress through 32000000; remainder final receipts','not_kernel_certified':True}
for f in ['ew','eta']:
 r=json.loads((L/f'outputs/{f}.json').read_text());assert all(x['equal' if f=='ew' else 'consistent'] for x in r['rows'])
 report[f]={'cases':len(r['rows']),'all_pass':True}
report['resource_failures']=['Initial 14-variable full run hit process cap with no completed-range receipt (not counted). Optimized full run hit cap after flushed completed=32000000; covered remainder in five completed bounded calls.','No C++ compiler available: bent.cpp not executed; Python replacement used.']
(L/'outputs/validation.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
