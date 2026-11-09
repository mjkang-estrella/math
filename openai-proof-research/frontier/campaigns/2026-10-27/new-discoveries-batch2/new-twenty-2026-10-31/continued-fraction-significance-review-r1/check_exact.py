import json,math,re,resource,os
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(10,10));resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
r=Path(__file__).resolve().parent;a=r.parent/'expanded-corpus-r45';s=(a/'Candidate.lean').read_text()
D=3049; lo=math.isqrt(D);assert lo==55 and lo**2<D<(lo+1)**2
m,d=55,2;seen={};states=[]
while (m,d) not in seen:
 assert len(states)<1000 and d>0
 seen[m,d]=len(states);q=(m+lo)//d
 assert q*d<=m+lo and m+lo+1<=(q+1)*d
 states.append([m,d,q]);mn=q*d-m;assert (D-mn*mn)%d==0;m,d=mn,(D-mn*mn)//d
assert (m,d)==(55,2) and len(states)==85
for name,k in [('M',0),('D',1),('A',2)]:
 v=list(map(int,re.search(r'def '+name+r'.*?:= !\[([^\]]+)\]',s).group(1).split(',')));assert v==[t[k] for t in states]
c=sorted({t[2] for t in states},reverse=True);assert c[6]==8 and 7*c[6]>states[0][2]
# d_i/2 is the absolute norm of the preceding standard convergent,
# with initial preceding convergent 1/0. Verify via exact p,q recurrence.
p0,p1,q0,q1=0,1,1,0
for i,(mi,di,ai) in enumerate(states):
 assert di==2*abs(p1*p1-55*p1*q1-6*q1*q1)
 p0,p1,q0,q1=p1,ai*p1+p0,q1,ai*q1+q0
out={'period':85,'return':[m,d],'states':states,'distinct_desc':c,'seventh':c[6],'gap_rational':'1/7','high_coefficient_norms':[{'coefficient':v,'norms':sorted({t[1]//2 for t in states if t[2]==v})} for v in c[:7]],'all_three_author_tables_equal':True,'exact_integer_arithmetic':True}
(r/'exact-check.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items() if k!='states'},indent=2))
