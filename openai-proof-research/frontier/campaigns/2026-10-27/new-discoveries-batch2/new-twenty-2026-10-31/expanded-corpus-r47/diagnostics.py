import resource,time,json,pathlib
resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(90,90))
p=pathlib.Path(__file__).resolve().parent
# Theorem 3 sequence, no assertion that diagnostic table formalizes game semantics.
def seq(c,N):
 a=[0,1]*c+[2,3]*c+[1,4]+[5,4]*(c-1)+[3,2]*c+[4,5]*c+[6,7]*c
 return [None]+[a[(n-1)%(12*c)]+8*((n-1)//(12*c)) for n in range(1,N+1)]
# exact ordered composition nim-sets, dynamic programming, not exponential partitions.
rows=[]
for c in [2,3,4,5,6]:
 N=150;g=seq(c,N); prev=[set() for _ in range(N+1)];prev[0]={0};first=[]
 for k in range(1,6*c+3):
  cur=[set() for _ in range(N+1)]
  for n in range(k,N+1):
   cur[n]={v^g[h] for h in range(1,n-k+2) for v in prev[n-h]}
  prev=cur
  if k==6*c+2:first=[n for n in range(k,N+1) if g[n] in cur[n]]
 rows.append({'c':c,'extra_cut':6*c+1,'part_count':6*c+2,'n_max':N,'conflicts':first,'max_nimset_cardinality':max(map(len,cur))});print(rows[-1],flush=True)
(p/'cut-diagnostic.json').write_text(json.dumps(rows,indent=2))
# Three elementary design mechanisms. Exact Walsh verification for existing codes and nonlinear products.
rows=[]
for d,m,t in [(7,4,3),(8,4,3),(9,4,3),(11,6,2)]:
 b=(2*m)//(2**t);cols=list(range(1,2**t))*b;cols += [0]*(d-len(cols));C=[y for y in range(2**d) if __import__('functools').reduce(int.__xor__,[cols[j] for j in range(d) if y>>j&1],0)==0]
 bad=[]
 for x in range(1,2**d):
  z=sum((-1)**((x&y).bit_count()%2) for y in C)
  if z and x.bit_count()!=m:bad.append(x)
 rows.append({'d':d,'m':m,'t':t,'size':len(C),'outside_level_nonzero':bad,'domination_counting_lower_bound':(2**d+d)//(d+1) if d%2 else None});print(rows[-1],flush=True)
(p/'design-diagnostic.json').write_text(json.dumps(rows,indent=2))
