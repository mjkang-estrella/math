import itertools,time,json,resource,os,math
resource.setrlimit(resource.RLIMIT_CPU,(110,110));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);start=time.time();p=1000003;n=7;nodes=[0,1,173];idx=list(itertools.product(range(3),range(n)))
rows=[[0 if k<j else math.factorial(k)//math.factorial(k-j)*pow(nodes[i],k-j,p)%p for k in range(n+1)]for i,j in idx]
rows.append([0]*n+[1]);count=0;bad=[]
def rank(rs):
 A=[r[:]for r in rs];r=0
 for j in range(n+1):
  k=next((k for k in range(r,len(A))if A[k][j]%p),None)
  if k is None:continue
  A[r],A[k]=A[k],A[r];q=pow(A[r][j],-1,p);A[r]=[a*q%p for a in A[r]]
  for k in range(r+1,len(A)):
   q=A[k][j];A[k]=[(a-q*b)%p for a,b in zip(A[k],A[r])]
  r+=1
 return r
for I in itertools.combinations(range(len(idx)),n):
 if any(sum(idx[i][1]>=n-k for i in I)>k for k in range(n+1)):continue
 count+=1;rs=[rows[i]for i in I]
 if rank(rs+[rows[-1]])!=n+1:bad.append({'indices':I,'kind':'degree_or_rank_modular_degeneracy'})
 else:
  for j in range(len(idx)):
   if j not in I and rank(rs+[rows[j]])!=n+1:bad.append({'indices':I,'forced_zero_modular':j});break
 if count%100==0:
  json.dump({'n':n,'m':3,'prime':p,'nodes':nodes,'maximal_patterns_checked':count,'modular_degeneracies':bad,'elapsed':time.time()-start,'complete':False},open('outputs/dope.json','w'),indent=2)
 if time.time()-start>100:break
else:complete=True
json.dump({'n':n,'m':3,'prime':p,'nodes':nodes,'maximal_patterns_checked':count,'modular_degeneracies':bad,'elapsed':time.time()-start,'complete':globals().get('complete',False)},open('outputs/dope.json','w'),indent=2)
print('checked',count,'degeneracies',len(bad),'complete',globals().get('complete',False))
