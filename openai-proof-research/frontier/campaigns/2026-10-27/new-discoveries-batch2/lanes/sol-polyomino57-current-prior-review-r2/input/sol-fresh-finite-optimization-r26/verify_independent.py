"""Independent streaming rooted-animal traversal and literal translation checker.
No imports from search code; no floating point or SAT solver.
"""
import os
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
import resource,signal,pathlib,json,time,hashlib
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(110,115));signal.alarm(125)
L=pathlib.Path(__file__).resolve().parent;start=time.monotonic()
C={(x,y) for x in range(-5,6) for y in range(-5,6) if abs(x)+abs(y)<=5 and (abs(x),abs(y))!=(2,2)}
assert len(C)==57
seen={next(iter(C))}
for _ in range(57):
 seen|={q for x,y in seen for q in [(x+1,y),(x-1,y),(x,y+1),(x,y-1)] if q in C}
assert seen==C
counts=[0]*12; histogram={};sha=hashlib.sha256();tight=[]
def neighbors(p):
 x,y=p;return [(x+1,y),(x-1,y),(x,y+1),(x,y-1)]
def allowed(p):return p[1]>0 or (p[1]==0 and p[0]>=0)
def visit(P,U,F):
 U=set(U);F=set(F)
 while U:
  p=min(U);U.remove(p);Q=P|{p};n=len(Q);counts[n]+=1
  if n==11:
   # Any containment sends distinguished cell (0,0) to a container cell.
   shifts=[t for t in sorted(C) if all((x+t[0],y+t[1]) in C for x,y in Q)]
   assert shifts,('NONEMBEDDABLE',sorted(Q))
   histogram[len(shifts)]=histogram.get(len(shifts),0)+1
   row=json.dumps([sorted(Q),shifts[0]],separators=(',',':'))+'\n'
   sha.update(row.encode());cert.write(row)
   if len(shifts)==1 and len(tight)<8:tight.append(sorted(Q))
  else:
   V=U|{q for q in neighbors(p) if allowed(q) and q not in Q and q not in F}
   visit(Q,V,F)
  F.add(p)
with (L/'embedding-certificate.jsonl').open('w') as cert:visit(set(),{(0,0)},set())
assert counts[1:]==[1,2,6,19,63,216,760,2725,9910,36446,135268]
result={'status':'PASS','method':'streaming rooted Redelmeier traversal; distinguished-cell translations','counts':counts[1:],'container':sorted(C),'size':len(C),'all_135268_have_literal_embedding':True,'embedding_count_histogram':histogram,'certificate_sha256':sha.hexdigest(),'tight_examples':tight,'elapsed_seconds':time.monotonic()-start,'arithmetic':'integer only','limits':{'address_space_bytes':512*1024**2,'cpu_seconds':110,'wall_alarm_seconds':125}}
(L/'independent-checks.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
