from pathlib import Path
import os,resource,signal,json,time,hashlib
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(30,35));signal.alarm(45)
L=Path(__file__).resolve().parent;D=L/'closure-path-data';D.mkdir(exist_ok=True);report=[]
def path(n,i):
 if n==1:return []
 m=n//2
 return [False]+path(m,i) if i<m else [True]+path(n-m,i-m)
def norm(P):
 x=min(a for a,b in P);y=min(b for a,b in P)
 return tuple(sorted((a-x,b-y) for a,b in P)),[-x,-y]
for n in [7,8,9,10]:
 t0=time.monotonic();target=[tuple(map(tuple,json.loads(s))) for s in (L/'data'/('layer%d.jsonl'%(n+1))).read_text().splitlines()];idx={P:i for i,P in enumerate(target)};edges=0
 out=D/('closure%d.jsonl'%n)
 with out.open('w') as f:
  for j,line in enumerate((L/'data'/('layer%d.jsonl'%n)).open()):
   P=set(map(tuple,json.loads(line)));bs=sorted({(x+dx,y+dy) for x,y in P for dx,dy in [(1,0),(-1,0),(0,1),(0,-1)]}-P);es=[]
   for b in bs:
    Q,shift=norm(P|{b});i=idx[Q];block=i//2048;leaf=(i%2048)//32;leaves=(min(2048,len(target)-block*2048)+31)//32
    p=path((len(target)+2047)//2048,block)+path(leaves,leaf)
    es.append([list(b),i,shift,p,i%32]);edges+=1
   f.write(json.dumps({'source_index':j,'edges':es},separators=(',',':'))+'\n')
 report.append(dict(source_size=n,source_rows=j+1,target_rows=len(target),edges=edges,sha256=hashlib.sha256(out.read_bytes()).hexdigest(),seconds=time.monotonic()-t0))
(L/'closure-path-data-receipt.json').write_text(json.dumps(dict(status='DATA_ONLY_NOT_KERNEL_PROOF',stages=report,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss),indent=2)+'\n')
