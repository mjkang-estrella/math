import os
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
import resource,signal,json,pathlib
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(15,20));signal.alarm(25)
L=pathlib.Path(__file__).resolve().parent
C={(x,y) for x in range(-5,6) for y in range(-5,6) if abs(x)+abs(y)<=5 and (abs(x),abs(y))!=(2,2)}
a=json.loads((L/'input/certificate-audit.json').read_text()); seen=set()
for r in a['deletion_obstructions']:
 c=tuple(r['cell']);P=set(map(tuple,r['piece']));assert c in C and c not in seen;seen.add(c)
 assert len(P)==11 and (0,0) in P
 reach={next(iter(P))}
 for _ in range(11):reach|={q for x,y in reach for q in [(x+1,y),(x-1,y),(x,y+1),(x,y-1)] if q in P}
 assert reach==P
 assert not any(all((x+dx,y+dy) in C-{c} for x,y in P) for dx,dy in C-{c})
assert seen==C
r=json.loads((L/'independent-receipt.json').read_text());i=json.loads((L/'input/independent-checks.json').read_text())
assert r['placement_histogram']==i['embedding_count_histogram']
(L/'ancillary-receipt.json').write_text(json.dumps({'status':'PASS','scope':'57 literal single-cell deletion obstructions only; no global optimum','deletion_obstructions':57,'placement_histograms_agree':True,'AS_bytes':512*1024**2,'CPU_seconds':[15,20],'wall_seconds':25,'BLAS_threads':1},indent=2))
