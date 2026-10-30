"""Independent exhaustive subset/partition and parity-side covering checks; no candidate imports."""
import itertools,json,pathlib,datetime
R=pathlib.Path(__file__).resolve().parent
def cube(d):
 return [sum(1<<(v^(1<<j)) for j in range(d)) for v in range(1<<d)]
def bits(s):
 while s:
  q=s&-s;yield q.bit_length()-1;s-=q
def cn(s,N,full):
 z=full
 for v in bits(s):z &= N[v]
 return z
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'method':'All independent subsets via include/exclude recursion, all Q3 proper set partitions, and Q5 parity-side exact covering. No symmetry quotient or candidate checker used.'}
for d in (3,4,5):
 N=cube(d);V=1<<d;full=(1<<V)-1;par=[sum(1<<v for v in range(V) if v.bit_count()%2==p) for p in (0,1)]
 stats={'nonempty_independent_subsets':0,'active':0,'max_independent':0,'maximum_sets':[],'weighted_violations':0}
 def visit(left,s):
  if not left:
   if not s:return
   k=s.bit_count();z=cn(s,N,full);stats['nonempty_independent_subsets']+=1
   if k>stats['max_independent']:stats['max_independent']=k;stats['maximum_sets']=[]
   if k==stats['max_independent']:stats['maximum_sets'].append(hex(s))
   if z:
    stats['active']+=1
    if k+z.bit_count()>d+1:stats['weighted_violations']+=1
   return
  b=left&-left;v=b.bit_length()-1
  visit(left^b,s);visit((left^b)&~N[v],s|b)
 visit(full,0)
 assert stats['max_independent']==V//2 and set(stats['maximum_sets'])==set(map(hex,par))
 assert stats['weighted_violations']==0
 # A parity class cannot occur in a TD coloring: no partition of its complement can help its own parity complement.
 for p in par:
  assert cn(p,N,full)==0
  assert all(N[v]&p==N[v] for v in bits(full^p))
 out['Q'+str(d)+'_subsets']=stats
# Enumerate literally all canonical proper partitions on Q3, then test the vertex-first TD quantifiers.
d=3;N=cube(d);full=255;stats={'proper_partitions':0,'TD_partitions':0,'minimum_TD_colors':9,'by_colors':{}}
def partitions(v,cs):
 if v==8:
  stats['proper_partitions']+=1
  if not all(any(C&N[x]==C for C in cs) for x in range(8)):return
  stats['TD_partitions']+=1;stats['minimum_TD_colors']=min(stats['minimum_TD_colors'],len(cs))
  stats['by_colors'][len(cs)]=stats['by_colors'].get(len(cs),0)+1
  act=[C for C in cs if cn(C,N,full)]
  reps=sum(C&-C for C in act)
  assert all(N[x]&reps for x in range(8))
  assert all(C.bit_count()<4 for C in cs if not cn(C,N,full))
  return
 for j,C in enumerate(cs):
  if not C&N[v]:partitions(v+1,cs[:j]+[C|(1<<v)]+cs[j+1:])
 partitions(v+1,cs+[1<<v])
partitions(0,[]);assert stats['minimum_TD_colors']==4;out['Q3_all_partitions']=stats
# Q5 total domination separates into two exact covering problems on parity sides.
N=cube(5);full=(1<<32)-1;P=[[v for v in range(32) if v.bit_count()%2==p] for p in (0,1)]
side=[];witness=[]
for p in (0,1):
 target=sum(1<<v for v in P[1-p]);tested={};chosen=None
 for k in range(5):
  count=0;found=[]
  for comb in itertools.combinations(P[p],k):
   z=0
   for v in comb:z|=N[v]
   count+=1
   if z==target:found.append(comb)
  tested[k]={'tested':count,'covers':len(found)}
  if found:chosen=found[0];break
 assert len(chosen)==4
 side.append(tested);witness.extend(chosen)
D=sum(1<<v for v in witness);cs=[1<<v for v in witness]+[sum(1<<v for v in P[p] if not D>>v&1) for p in (0,1)]
assert all(cs) and len(cs)==10 and sum(cs)==full
assert all(not any(N[v]&C for v in bits(C)) for C in cs)
assert all(any(C&N[v]==C for C in cs) for v in range(32))
out['Q5_exact_gamma_and_upper']={'side_searches':side,'gamma_t':8,'TD_10_colors':[hex(C) for C in cs]}
# Exact integer margins, including non-target dimensions as controls, no floating point.
out['margins']=[]
for n in range(2,9):
 d=(1<<n)+1;V=1<<d;g=1<<(d-n)
 m1=3*V//2+1-(d+1)*g;m0=2*V-(d+1)*(g+1)
 assert m1>0 and m0>0
 out['margins'].append({'n':n,'d':d,'one_inactive_margin':m1,'zero_inactive_margin':m0})
(R/'independent-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
