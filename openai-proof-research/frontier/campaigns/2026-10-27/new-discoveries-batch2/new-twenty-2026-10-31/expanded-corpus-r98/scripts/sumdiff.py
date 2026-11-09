from pathlib import Path
import json,subprocess,sys
D=Path(__file__).resolve().parents[1];sat='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/cadical'
e=int(sys.argv[1]); mode=sys.argv[2];cs=[];nv=e
# sx & sy implies s(x+y) or s(x-y), ordered pairs
for x in range(e):
 for y in range(e):cs.append([-x-1,-y-1,(x+y)%e+1,(x-y)%e+1])
# xor chain, enforcing odd cardinality
last=1
for x in range(2,e+1):
 nv+=1; a,b,c=last,x,nv
 cs += [[a,b,-c],[-a,-b,-c],[a,-b,c],[-a,b,c]];last=c
cs.append([last])
if mode=='zero':cs.append([-1])
else:
 # disjunction of differences s(x) != s(-x)
 ds=[]
 for x in range(1,(e+1)//2):
  nv+=1;a,b,c=x+1,e-x+1,nv
  cs += [[a,b,-c],[-a,-b,-c],[a,-b,c],[-a,b,c]];ds.append(c)
 cs.append(ds)
p=D/f'outputs/sumdiff-{e}-{mode}.cnf';p.write_text(f'p cnf {nv} {len(cs)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in cs))
r=subprocess.run([sat,'-t','8',str(p)],capture_output=True,text=True);(D/f'outputs/sumdiff-{e}-{mode}.solver').write_text(r.stdout+r.stderr)
print(e,mode,r.returncode, next((l for l in r.stdout.splitlines() if l.startswith('s ')),'unknown'),flush=True)
if r.returncode==10:
 pos={int(v) for l in r.stdout.splitlines() if l.startswith('v ') for v in l[2:].split() if int(v)>0};S=[x for x in range(e) if x+1 in pos];assert len(S)%2 and all((x+y)%e in S or (x-y)%e in S for x in S for y in S);print('WITNESS',S,flush=True)
