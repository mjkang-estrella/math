import sys,subprocess,json
from pathlib import Path
D=Path(__file__).resolve().parents[1];m=int(sys.argv[1]);r=int(sys.argv[2]);nv=m;cs=[[1]];sums=[[] for _ in range(m)]
for x in range(m):
 for y in range(x,m):
  if x==y:v=x+1
  else:
   nv+=1;v=nv;cs += [[-v,x+1],[-v,y+1],[-x-1,-y-1,v]]
  sums[(x+y)%m]+=[v]*(1 if x==y else 2)
for vs in sums:
 cs.append(list(set(vs)));prev=[]
 for v in vs:
  curr=[]
  for j in range(1,min(len(prev)+1,r+1)+1):
   nv+=1;q=nv;curr.append(q)
   if j<=len(prev):cs.append([-prev[j-1],q])
   cs.append(([-v,q] if j==1 else [-v,-prev[j-2],q]))
  prev=curr
 if len(prev)>r:cs.append([-prev[r]])
p=D/f'outputs/ruzsa-{m}-{r}.cnf';p.write_text(f'p cnf {nv} {len(cs)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in cs))
sat='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/cadical';pout=subprocess.run([sat,'-t','6',str(p)],capture_output=True,text=True);(D/f'outputs/ruzsa-{m}-{r}.solver').write_text(pout.stdout+pout.stderr)
o=dict(m=m,r=r,status=pout.returncode)
if pout.returncode==10:
 pos={int(x) for l in pout.stdout.splitlines() if l.startswith('v ') for x in l[2:].split() if int(x)>0};A=[i for i in range(m) if i+1 in pos];counts=[sum((x+y)%m==z for x in A for y in A) for z in range(m)];assert min(counts)>=1 and max(counts)<=r;o.update(A=A,counts=counts)
print(json.dumps(o),flush=True)
