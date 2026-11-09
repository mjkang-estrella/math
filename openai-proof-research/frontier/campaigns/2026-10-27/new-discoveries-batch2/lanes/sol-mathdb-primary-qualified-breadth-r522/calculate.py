from itertools import permutations,combinations
from collections import Counter
import pathlib,json
P=pathlib.Path(__file__).resolve().parent
# Direct right-greedy simulation; stack list is bottom to top.
def sc(pi):
 stack=[];out=[]
 for x in pi:
  while any(x<stack[j+1]<stack[j] for j in range(len(stack)-1)):out.append(stack.pop())
  stack.append(x)
 return tuple(out+stack[::-1])
stack=[]
for n in range(3,9):
 c=Counter(sc(p) for p in permutations(range(1,n+1)));vs=sorted(set(c.values()),reverse=True)
 stack.append({'n':n,'inputs':sum(c.values()),'largest':vs[0],'largest_outputs':[list(k) for k,v in c.items() if v==vs[0]],'second':vs[1],'second_multiplicity':sum(v==vs[1] for v in c.values())})
# Every strict ordering on six unordered pairs is represented; no metric assumption.
n=4;edges=list(combinations(range(n),2));hist=Counter()
for order in permutations(edges):
 ranks={e:i+1 for i,e in enumerate(order)};balls=set()
 for c in range(n):
  s={c};balls.add(frozenset(s))
  for v in sorted((v for v in range(n) if v!=c),key=lambda v:ranks[tuple(sorted((c,v)))]):s.add(v);balls.add(frozenset(s))
 hist[len(balls)]+=1
# Known parity issue: all labeled Hamilton paths on balanced K4.
plus={(0,1),(0,2),(0,3)}
values=Counter(sum(1 if tuple(sorted((p[i],p[i+1]))) in plus else -1 for i in range(3)) for p in permutations(range(4)))
result={'stack_finite_diagnostic':stack,'ball_n4_all_720_edge_orders':dict(hist),'balanced_K4_P4_imbalance':dict(values),'scope':'Executed exact finite checks only; no general proof, novelty or equality-Hasse classification.'}
(P/'calculations.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
# Read bound context selectively, without treating omitted histories as reviewed.
ids={r['mathdb_id'] for r in json.loads((P/'records.json').read_text())};L=P.parent;B=L.parent
context={}
for p in [L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 obj=json.loads(p.read_text());context[str(p)]={'top_type':type(obj).__name__,'matches':[]}
 def walk(x):
  if isinstance(x,dict):
   if any(str(i) in json.dumps(x,ensure_ascii=False) for i in ids) and not any(isinstance(v,(list,dict)) for v in x.values()):context[str(p)]['matches'].append(x)
   for v in x.values():walk(v)
  elif isinstance(x,list):
   for v in x:walk(v)
 walk(obj)
ledger=json.loads((B/'ledger.json').read_text());context['accepted']=[{'number':a['number'],'title':a['title']} for a in ledger['accepted']]
context['prior_context_top_keys']=list(json.loads((B/'prior-campaign-context.json').read_text()))
(P/'context-screen.json').write_text(json.dumps(context,indent=2)+'\n');print(json.dumps(context))
