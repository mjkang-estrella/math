"""Exact bounded verification; no candidate code imported. Run from this lane."""
import os
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'): os.environ[k]='1'
import resource,signal,time,json,pathlib,hashlib
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(150,155));signal.alarm(170)
start=time.monotonic();L=pathlib.Path(__file__).resolve().parent
S=16; COL=sum(1<<(S*y) for y in range(16))
def norm(m):
 m >>= ((m&-m).bit_length()-1)//S*S
 cols=0;t=m
 while t: cols |= t&65535;t>>=S
 return m >> ((cols&-cols).bit_length()-1)
def encode(P):
 a=min(x for x,y in P);b=min(y for x,y in P)
 return sum(1<<((y-b)*S+x-a) for x,y in P)
def points(m):
 out=[]
 while m:
  b=m&-m;i=b.bit_length()-1;out.append((i%S,i//S));m-=b
 return out
def conn(P):
 P=set(P);todo=[next(iter(P))];seen=set(todo)
 while todo:
  x,y=todo.pop()
  for q in ((x+1,y),(x-1,y),(x,y+1),(x,y-1)):
   if q in P and q not in seen:seen.add(q);todo.append(q)
 return seen==P
C={(x+5,y+5) for x in range(-5,6) for y in range(-5,6) if abs(x)+abs(y)<=5 and not(abs(x)==abs(y)==2)}
assert len(C)==57 and conn(C)
CM=sum(1<<(y*S+x) for x,y in C)
layer={1};counts=[1]
for n in range(2,12):
 nxt=set()
 for p in layer:
  # One-cell padding prevents row wrap and negative shifts; width/height <=10 here.
  q=p<<(S+1);front=((q<<1)|(q>>1)|(q<<S)|(q>>S))&~q
  while front:
   bit=front&-front;front-=bit;nxt.add(norm(q|bit))
 layer=nxt;counts.append(len(layer));print('layer',n,len(layer),flush=True)
assert counts==[1,2,6,19,63,216,760,2725,9910,36446,135268]
cert=set();literal=0;holed=0
for line in (L/'input/embedding-certificate.jsonl').open():
 P,t=json.loads(line);P=list(map(tuple,P));assert len(P)==len(set(P))==11 and conn(P)
 assert all((x+t[0]+5,y+t[1]+5) in C for x,y in P)
 p=encode(P);assert p not in cert;cert.add(p);literal+=1
assert cert==layer
hist={};boxhist={};hard=0
for p in sorted(layer):
 P=points(p);assert len(P)==11 and conn(P)
 w=1+max(x for x,y in P);h=1+max(y for x,y in P)
 assert w<=11 and h<=11 and w+h<=12
 boxhist[str((w,h))]=boxhist.get(str((w,h)),0)+1
 if min(w,h)>=4:hard+=1
 placements=0
 # Any translation into C must have its tight bounding box in [0,10]^2.
 for dy in range(12-h):
  for dx in range(12-w):
   q=p<<(S*dy+dx)
   if q&CM==q:placements+=1
 assert placements,('FALSIFIER',P)
 hist[placements]=hist.get(placements,0)+1
# Explicit connected holed input is included: 3x3 ring plus three exterior cells.
ring={(x,y) for x in range(3) for y in range(3)}-{(1,1)}
ring|={(3,0),(4,0),(5,0)}
assert conn(ring) and encode(ring) in layer
# Canonical masks serialize unambiguously, independent of certificate ordering.
digest=hashlib.sha256(('\n'.join(map(str,sorted(layer)))+'\n').encode()).hexdigest()
out={'status':'PASS','scope':'exact all connected 11-cell Z2 sets modulo translations, holes allowed; no optimality','method':'16-bit-row integer bitboard neighbor closure and bounding-box shift subset tests','counts':counts,'container_size':len(C),'container_connected':True,'literal_witnesses_checked':literal,'terminal_set_equality':True,'independently_embedded':len(layer),'hard_box_cases':hard,'placement_histogram':hist,'bounding_box_histogram':boxhist,'holed_test':True,'canonical_family_sha256':digest,'seconds':time.monotonic()-start,'limits':{'AS_bytes':512*1024**2,'CPU_seconds':[150,155],'wall_alarm_seconds':170,'BLAS_threads':1},'kernel_verified':False}
(L/'independent-receipt.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
