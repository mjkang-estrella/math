import pathlib,json,time,collections
from transfer import PERMS,transform,canonical
L=pathlib.Path(__file__).parent;start=time.monotonic();ceiling=175
F=json.loads((L/'F-table.json').read_text());C=json.loads((L/'C-table.json').read_text())
expanded={}
for r in F['rows']:
 for p in PERMS:
  s=transform(r['state'],p);v=(r['cost'],tuple(p[c] for c in r['colors']))
  if s not in expanded or v[0]<expanded[s][0]:expanded[s]=v
rows=[(s,*v) for s,v in expanded.items()]
indices={}
for ports in [(2,3),(0,2),(0,),(0,1,2)]:
 d=collections.defaultdict(list)
 for s,c,w in rows:d[tuple(s[i][0] for i in ports)].append((s,c,w))
 indices[ports]=d
print('expanded F',len(rows),flush=True)
calls=0;states={};completions=0;complete=True
def options(req,budget):
 global calls
 calls+=1
 if calls%1000==0 and time.monotonic()-start>ceiling:raise TimeoutError('175s composition ceiling')
 ports=tuple(sorted(req));idx=indices[ports];key=tuple(req[i][0] for i in ports)
 for s,c,w in idx.get(key,[]):
  if c>budget:continue
  d=c+sum((s[i][1]|req[i][1]).bit_count()==4 for i in ports)
  if d<=budget:yield s,d,w
try:
 for cr in C['rows']:
  cs=cr['state'];base=cr['cost']
  for a,da,wa in options({2:cs[0],3:cs[1]},2-base):
   for d,dd,wd in options({0:cs[5],2:a[0]},2-base-da):
    for c,dc,wc in options({0:cs[4],2:d[1]},2-base-da-dd):
     for b,db,wb in options({0:cs[3],1:cs[2],2:c[1]},2-base-da-dd-dc):
      completions+=1;cost=base+da+dd+dc+db
      state=(a[1],b[3],c[3],d[3])
      # Canonicalize only once for each raw state, after the search.
      if state not in states or cost<states[state]['cost']:
       states[state]={'state':state,'cost':cost,'children':[wa,wb,wc,wd,cr['colors']]}
except TimeoutError as e:complete=False;print(str(e),flush=True)
out={'complete':complete,'cap':2,'expanded_F':len(rows),'calls':calls,'completions':completions,'raw_states':len(states),'cost_counts':dict(collections.Counter(r['cost'] for r in states.values())),'seconds':time.monotonic()-start,'rows':list(states.values())}
(L/'L-table.json').write_text(json.dumps(out,separators=(',',':')))
print({k:v for k,v in out.items() if k!='rows'},flush=True)
