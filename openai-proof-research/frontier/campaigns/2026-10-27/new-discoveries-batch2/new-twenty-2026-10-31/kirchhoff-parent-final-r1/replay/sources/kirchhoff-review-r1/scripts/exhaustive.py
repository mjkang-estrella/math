from pathlib import Path
import sys,json,runpy,time
D=Path(__file__).resolve().parents[1]
# Load independent functions only (no packet code).
s=(D/'scripts/exact.py').read_text().split('witness=list(')[0]
x={"__file__":str(D/"scripts/exact.py")};exec(compile(s,'exact-functions','exec'),x)
calc=x['calc'];serial=x['serial'];connected=x['connected']
n=int(sys.argv[1]);lines=(D/f'outputs/graph{n}c.g6').read_bytes().splitlines()
start=time.monotonic();fail={'MP':[],'spectral':[]};eq={'MP':[],'spectral':[]};seen=0
for line in lines:
 if not line:continue
 assert line[0]-63==n
 bits=[(v-63)>>k&1 for v in line[1:] for k in range(5,-1,-1)]
 pairs=[(i,j) for j in range(1,n) for i in range(j)]
 edges=[e for e,b in zip(pairs,bits) if b];assert connected(n,edges)
 rs={a:calc(n,edges,a)[:2] for a in [-1,0,1]}
 deg=[sum(i in e for e in edges) for i in range(n)];regular=len(set(deg))==1
 for k,mode in enumerate(['MP','spectral']):
  if not rs[-1][k]<=rs[0][k]<=rs[1][k]:fail[mode].append(dict(graph6=line.decode(),values=rs))
  if any((rs[a][k]==rs[0][k])!=regular for a in [-1,1]):eq[mode].append(line.decode())
 seen+=1
 if seen%100==0:print(seen,flush=True)
r=dict(n=n,count=seen,ordering_failures=fail,equality_failures=eq,seconds=time.monotonic()-start)
(D/f'outputs/exhaustive-{n}.json').write_text(json.dumps(serial(r),indent=2))
print('DONE',n,seen,{k:len(v) for k,v in fail.items()},r['seconds'])
