import itertools,json,time,resource,os,random
resource.setrlimit(resource.RLIMIT_CPU,(110,110));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);start=time.time();out={'exhaustive':{},'structured':{},'counterexamples':[]};rng=random.Random(356988)
def conflicts(n,E):
 out=[set()for _ in range(n)];inc=[set()for _ in range(n)]
 for a,b in E:out[a].add(b);inc[b].add(a)
 return {(a,b)for a in range(n)for b in range(a+1,n)if b in out[a] or a in out[b] or out[a]&inc[b] or out[b]&inc[a]}
def clique(n,E):return len(conflicts(n,E))==n*(n-1)//2
def possible(n,E):
 # Necessary: removing any arc must create at least 2 nonconflicting pairs to save two colours.
 for e in E:
  c=conflicts(n,E-{e})
  if n*(n-1)//2-len(c)<2:return False
 return True
for n in [2,4]:
 pairs=list(itertools.combinations(range(n),2));count=cl=survive=0
 for v in itertools.product(range(3),repeat=len(pairs)):
  E={((a,b)if d==1 else(b,a))for (a,b),d in zip(pairs,v)if d};count+=1
  if clique(n,E):
   cl+=1
   if possible(n,E):survive+=1;out['counterexamples'].append({'n':n,'edges':list(E),'status':'necessary_conditions_only'})
 out['exhaustive'][n]={'oriented_graphs':count,'absolute_cliques':cl,'necessary_survivors':survive}
for n in [6,8,10,12,14,16,18,20,22,24,26,28,30,32]:
 count=cl=survive=0
 for it in range(2000):
  # odd circulant with one vertex deleted, and random perturbation
  N=n+1;S=[k if rng.randrange(2)else N-k for k in range(1,(N+1)//2) if rng.random()<.5]
  E={(a,b)for a in range(n)for b in range(n)if (b-a)%N in S};count+=1
  if clique(n,E):
   cl+=1
   if possible(n,E):survive+=1;out['counterexamples'].append({'n':n,'edges':list(E),'status':'necessary_conditions_only'})
  if time.time()-start>100:break
 out['structured'][n]={'deleted_odd_circulants':count,'absolute_cliques':cl,'necessary_survivors':survive};json.dump(out,open('outputs/oriented.json','w'),indent=2)
 if time.time()-start>100:break
out['seconds']=time.time()-start;json.dump(out,open('outputs/oriented.json','w'),indent=2);print(out)
