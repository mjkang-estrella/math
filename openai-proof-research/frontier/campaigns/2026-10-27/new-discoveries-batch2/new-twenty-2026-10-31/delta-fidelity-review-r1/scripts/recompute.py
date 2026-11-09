import ast, collections, itertools, json, pathlib, re
lane=pathlib.Path(__file__).resolve().parent.parent
# Parse only explicit data, never import or execute packet code.
src=(lane/'fresh/lean/Nodes.lean').read_text()
rows={int(k):tuple(map(tuple,ast.literal_eval(v))) for k,v in re.findall(r'def rows(\d+) : Delta153.Graph := (\[.*\])',src)}
def valid(g):
 n=len(g)
 assert all(len(r)==n and sum(r)==6 for r in g)
 assert all(g[i][i]==0 for i in range(n))
 assert all(g[i][j]==g[j][i]>=0 for i in range(n) for j in range(n))
def centers(g):
 return [i for i,r in enumerate(g) if sorted(x for x in r if x)!=[ ] and sorted(x for x in r if x)==[2,2,2]]
def down(g,x):
 assert x in centers(g)
 ns={i for i,m in enumerate(g[x]) if m}
 keep=[i for i in range(len(g)) if i!=x]
 h=tuple(tuple(g[i][j]+int(i!=j and i in ns and j in ns) for j in keep) for i in keep)
 valid(h); return h
def up(g,t):
 assert len(set(t))==3 and all(g[a][b]>0 for a,b in itertools.combinations(t,2))
 n=len(g); ts=set(t)
 h=tuple(tuple(g[i][j]-int(i!=j and i in ts and j in ts) for j in range(n))+(2 if i in ts else 0,) for i in range(n))+(tuple(2 if i in ts else 0 for i in range(n))+(0,),)
 valid(h); return h
valid(rows[0]); assert all(x in (0,2) for r in rows[0] for x in r)
seen={rows[0]}; todo=[rows[0]]; arcs=0
while todo:
 g=todo.pop()
 for x in centers(g):
  h=down(g,x); arcs+=1
  if h not in seen: seen.add(h); todo.append(h)
hist=collections.Counter(map(len,seen)); assert len(seen)==2328 and arcs==9846 and min(hist)==11
p=rows[0]
for i,x in enumerate([0,0,3,4,6,7,11],1):
 p=down(p,x); assert p==rows[i]
g7=p
orders=[len(p)]
for i,(kind,arg) in enumerate([('up',(1,6,8)),('down',6),('up',(4,7,10)),('up',(3,7,10)),('down',10),('down',7),('down',9)],8):
 p=up(p,arg) if kind=='up' else down(p,arg)
 assert p==rows[i]; orders.append(len(p))
assert len(p)==10

def has_chain(g):
 n=len(g); V=range(n)
 regular={i for i in V if sum(g[i])==6}
 ends={i for i in regular if sum(m>0 for m in g[i])==4 and max(g[i])<=2}
 budget={(i,j):g[i][j] for i in V for j in range(i+1,n)}
 def reserve(cap,es):
  cnt=collections.Counter(tuple(sorted(e)) for e in es)
  if any(a==b or cnt[a,b]>cap.get((a,b),0) for a,b in cnt): return None
  out=cap.copy()
  for e,k in cnt.items(): out[e]-=k
  return out
 def tri(a,b,c): return [(a,b),(a,c),(b,c)]
 def doubles(cap,a,count):
  opts=[v for v in V if v!=a and cap[tuple(sorted((a,v)))]>=2]
  for vs in itertools.combinations_with_replacement(opts,count):
   es=[(a,v) for v in vs for _ in range(2)]
   h=reserve(cap,es)
   if h is not None: yield h,vs
 def extend(cap,b,bases,triangles):
  if b in ends:
   for h,vs in doubles(cap,b,2): return {'bases':bases,'triangles':triangles,'right':vs}
  if len(bases)==n: return None
  for cap1,att in doubles(cap,b,1):
   for v in V:
    if v in bases or v not in regular: continue
    for t in V:
     h=reserve(cap1,tri(b,v,t))
     if h is not None:
      found=extend(h,v,bases+[v],triangles+[(b,v,t)])
      if found is not None: return found
  return None
 for a in sorted(ends):
  for b in V:
   if b==a or b not in regular: continue
   for c in V:
    h=reserve(budget,tri(a,b,c))
    if h is None: continue
    for h2,left in doubles(h,a,2):
     found=extend(h2,b,[a,b],[(a,b,c)])
     if found is not None: return found
 return None
assert has_chain(g7) is None
mins=[g for g in seen if len(g)==11]
assert all(has_chain(g) is None for g in mins)
# Controls instantiate exactly the edge-capacity semantics, including aliasing.
controls={}
for fn,name in [('Controls','control'),('AliasControl','alias')]:
 text=(lane/f'fresh/lean/{fn}.lean').read_text()
 data=ast.literal_eval(re.search(r'def rows : Delta153.Graph :=\s*(\[.*?\])\s*def',text,re.S).group(1))
 witness=has_chain(data); assert witness is not None
 controls[name]=witness
assert data[1][3]==3
out={'states':len(seen),'arcs':arcs,'histogram':dict(sorted(hist.items())), 'pure_minimum':min(hist),'minimum_states':len(mins),'g7_has_chain':False,'all_minima_chain_free':True,'seven_move_orders':orders,'controls':controls,'g7':g7,'order10':p}
(lane/'numerical.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
