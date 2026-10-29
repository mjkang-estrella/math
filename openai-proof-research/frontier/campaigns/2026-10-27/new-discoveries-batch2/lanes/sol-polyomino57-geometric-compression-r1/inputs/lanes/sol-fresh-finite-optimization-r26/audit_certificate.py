import os
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
import resource,signal,pathlib,json,hashlib,time
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(90,95));signal.alarm(105)
L=pathlib.Path(__file__).resolve().parent;start=time.monotonic()
C={(x,y) for x in range(-5,6) for y in range(-5,6) if abs(x)+abs(y)<=5}-{(a,b) for a in [-2,2] for b in [-2,2]}
rows=set();forced={}; hist={};boxhist={}
for line in (L/'embedding-certificate.jsonl').open():
 pts,t=json.loads(line);P=set(map(tuple,pts));assert len(P)==11
 assert all((x+t[0],y+t[1]) in C for x,y in P)
 minx=min(x for x,y in P);miny=min(y for x,y in P)
 key=tuple(sorted((x-minx,y-miny) for x,y in P));assert key not in rows;rows.add(key)
 w=max(x for x,y in P)-minx+1;h=max(y for x,y in P)-miny+1
 boxhist[str((w,h))]=boxhist.get(str((w,h)),0)+1
 V=[{(x+a,y+b) for x,y in P} for a,b in C if all((x+a,y+b) in C for x,y in P)]
 core=set.intersection(*V)
 for c in core:
  if c not in forced:forced[c]=sorted(P)
assert len(rows)==135268
# Independently check completeness by growth, then literal equality of terminal sets.
layer={((0,0),)}
for n in range(2,12):
 nxt=set()
 for P in layer:
  S=set(P)
  for x,y in P:
   for c in [(x+1,y),(x-1,y),(x,y+1),(x,y-1)]:
    if c in S:continue
    Q=S|{c};a=min(x for x,y in Q);b=min(y for x,y in Q)
    nxt.add(tuple(sorted((x-a,y-b) for x,y in Q)))
 layer=nxt
assert layer==rows
out={'status':'PASS','certificate_rows':len(rows),'coverage':'exact set equality with independently normalized neighbor-growth family','inclusion_minimal':len(forced)==57,'forced_cells':len(forced),'deletion_obstructions':[{'cell':c,'piece':v} for c,v in sorted(forced.items())],'bounding_box_histogram':boxhist,'elapsed_seconds':time.monotonic()-start}
(L/'certificate-audit.json').write_text(json.dumps(out,indent=2));print('PASS',len(rows),'forced',len(forced),'seconds',out['elapsed_seconds'])
