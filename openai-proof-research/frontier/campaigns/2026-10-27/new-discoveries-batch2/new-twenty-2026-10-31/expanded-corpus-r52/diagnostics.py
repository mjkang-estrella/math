import math,json,pathlib,resource,os
R=pathlib.Path(__file__).resolve().parent;resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(30,30));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
# All are diagnostics, not Lean semantics or a certificate of a universal claim.
checks=[]
for N in range(4,161):
 for m in range(1,N//2):
  vals=[(math.sin((2*m+1)*math.pi*j/N)/(2*math.sin(math.pi*j/N)),j) for j in range(2,N//2+1)]
  v=min(x for x,j in vals);j=min(j for x,j in vals if x <= v+1e-10)
  bound=math.ceil((3*N)/(4*m+2)-.5)
  checks.append({'N':N,'m':m,'principal_index_tolerance':j,'bound':bound,'diagnostic_violation':j>bound})
(R/'spectral-diagnostic.json').write_text(json.dumps({'warning':'double precision diagnostic only; tolerance handles exact ties without certification','checks':checks},indent=2)+'\n')
# Recurrence exact integer arithmetic of coefficients for a=b=c=1.
c=[1,-1]
for n in range(62):c.append(-c[-1]-c[-2])
print('spectral pairs',len(checks),'violations',sum(x['diagnostic_violation'] for x in checks));print('Taylor constant coefficients',c);print('P_(3k+2)(0)=0 in these exact diagnostics; universal proof is Taylor.lean')
