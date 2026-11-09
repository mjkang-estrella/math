import pathlib,json,itertools,collections,time
L=pathlib.Path(__file__).parent;start=time.monotonic();P=list(itertools.permutations(range(5)))
def expand(states):
 out=set()
 for s in states:
  for p in P:out.add(tuple((p[c],sum(1<<p[j] for j in range(5) if m>>j&1)) for c,m in s))
 return out
F=expand([r['state'] for r in json.loads((L/'F-table.json').read_text())['rows'] if r['cost']==0])
C=[tuple(map(tuple,r['state'])) for r in json.loads((L/'C-table.json').read_text())['rows'] if r['cost']==0]
lj=[((0,0),(3,2)),((0,2),(4,0)),((0,3),(4,1)),((1,1),(4,2)),((1,0),(4,3)),((2,0),(4,4)),((3,0),(4,5)),((1,2),(2,1)),((2,2),(3,1))]
gj=[((0,0),(2,2)),((0,1),(1,1)),((0,2),(3,0)),((0,3),(3,1)),((1,0),(3,2)),((1,2),(3,4)),((2,1),(3,3)),((2,0),(3,5)),((1,3),(2,3))]
def solve(domains,joins,ports,order):
 assigned={};answers=set();visits=0
 def dfs(pos):
  nonlocal visits
  visits+=1
  if pos==len(order):answers.add(tuple(assigned[a][i] for a,i in ports));return
  a=order[pos];req=[]
  for (b,i),(c,j) in joins:
   if a==b and c in assigned:req.append((i,assigned[c][j]))
   if a==c and b in assigned:req.append((j,assigned[b][i]))
  for row in domains[a]:
   if all(row[i][0]==col and (row[i][1]|mask).bit_count()!=4 for i,(col,mask) in req):assigned[a]=row;dfs(pos+1)
  assigned.pop(a,None)
 dfs(0);return answers,visits
ls,lv=solve([F,F,F,F,C],lj,[(0,1),(1,3),(2,3),(3,3)],[4,1,2,3,0])
le=expand(ls)
expected=expand([r['state'] for r in json.loads((L/'L-table.json').read_text())['rows'] if r['cost']==0]);assert le==expected
gs,gv=solve([le,le,le,C],gj,[],[3,1,0,2]);assert not gs
out={'pass':True,'normal_F_labelled_states':len(F),'normal_C_global_orbits':len(C),'normal_L_raw_states':len(ls),'normal_L_labelled_states':len(le),'L_search_nodes':lv,'G_search_nodes':gv,'normal_G_states':len(gs),'different_composition_order':True,'seconds':time.monotonic()-start,'meaning':'local exact multipole no-normal-coloring replay; not a DRAT replay'}
(L/'zero-verification.json').write_text(json.dumps(out,indent=2));print(out)
