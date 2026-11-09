import itertools,time,json,sys
from fractions import Fraction
sys.setrecursionlimit(1000000)
start=time.monotonic(); checked=0;states=0;rows=[]
def sched(a):
 global states
 colors={}; edges=0
 def dfs(s):
  global states
  colors[s]=1;states+=1
  for j in range(len(a)):
   if any(s[i]+1>=a[i] for i in range(len(a)) if i!=j):continue
   t=tuple(0 if i==j else s[i]+1 for i in range(len(a)))
   c=colors.get(t,0)
   if c==1:return True
   if c==0 and dfs(t):return True
  colors[s]=2;return False
 return dfs((0,)*len(a)),len(colors)
maxa=int(sys.argv[1]); maxk=int(sys.argv[2]);mini=int(sys.argv[3])
for k in range(2,maxk+1):
 cnt=0;maxstates=0
 for a in itertools.combinations_with_replacement(range(mini,maxa+1),k):
  if time.monotonic()-start>110:print(json.dumps({'partial':True,'k':k,'last':a,'checked':checked,'states':states}),flush=True);sys.exit()
  d=sum((Fraction(1,x) for x in a),Fraction())
  if d>1-Fraction(a[0]-1,a[0]*(a[0]+1)):continue
  result,ns=sched(a);checked+=1;cnt+=1;maxstates=max(maxstates,ns)
  if not result:print('COUNTEREXAMPLE',a,str(d),flush=True);sys.exit()
 print(json.dumps({'k':k,'period_min':mini,'period_max':maxa,'qualifying_instances':cnt,'max_visited_states':maxstates,'cumulative_states':states,'no_counterexample':True}),flush=True)
