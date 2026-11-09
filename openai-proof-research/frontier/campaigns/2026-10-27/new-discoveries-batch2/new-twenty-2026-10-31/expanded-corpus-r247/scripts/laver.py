import os,resource,time,json,pathlib
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]));L=pathlib.Path(__file__).resolve().parents[1];st=time.monotonic();out=[]
for n in range(9):
 N=1<<n;A=[[0]*(N+1) for _ in range(N+1)];A[N]=list(range(N+1))
 for x in range(N-1,0,-1):
  A[x][1]=x+1
  for y in range(1,N):A[x][y+1]=A[A[x][y]][x+1]
 M=[None]*(N+1);M[N]=[None]+[list(range(1,y+1)) for y in range(1,N+1)];count=0;fail=None
 for x in range(N-1,0,-1):
  M[x]=[None,[-i for i in range(1,x+1)]+[1]]
  for y in range(1,N):
   prev=M[x][y]; seq=M[A[x][y]][x+1]
   M[x].append([-z if 0<z<=x else (y+1 if z==x+1 else prev[-z-1]) for z in seq])
 for x in range(1,N+1):
  for y in range(1,N+1):
   assert len(M[x][y])==A[x][y]
   for ell,z in enumerate(M[x][y],1):
    v=A[x][z] if z>0 else -z
    if (v-1)&~(ell-1):fail=[n,x,y,ell,z,v];break
    count+=1
   if fail:break
  if fail:break
 r={'n':n,'order':N,'triples_checked':count,'failure':fail,'seconds':time.monotonic()-st};out.append(r);print(json.dumps(r),flush=True)
 if n==3:
  expected=[[-1,1,-1,2,-1,3,-1,4],[-1,-2,1,2,-1,-2,3,4],[-1,-2,-3,1,-1,-2,-3,2],[-1,-2,-3,-4,1,2,3,4],[-1,-2,-3,-4,-5,1,-5,2],[-1,-2,-3,-4,-5,-6,1,2],[-1,-2,-3,-4,-5,-6,-7,1],[1,2,3,4,5,6,7,8]]
  periods=[next(y for y in range(1,N+1) if A[x][y]==N) for x in range(1,N+1)]
  assert [M[x][periods[x-1]] for x in range(1,N+1)]==expected
 if fail or time.monotonic()-st>95:break
 del M,A
(L/'laver-results.json').write_text(json.dumps({'definition':'Proposition 6.3; ST is binary subset relation on x-1,y-1','printed_FM3_reproduced':True,'rows':out},indent=2))
