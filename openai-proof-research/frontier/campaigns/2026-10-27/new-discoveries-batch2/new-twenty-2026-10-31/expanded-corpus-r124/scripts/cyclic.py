import random,subprocess,pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];solver='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/cadical';rng=random.Random(124)
def check(n,A,tag):
 clauses=[];nvars=n
 def xor(a,b):
  nonlocal nvars
  nvars+=1;z=nvars;clauses.extend([[-a,-b,-z],[a,b,-z],[a,-b,z],[-a,b,z]]);return z
 def parity(xs):
  if not xs:
   nonlocal nvars
   nvars+=1;clauses.append([-nvars]);return nvars
  x=xs[0]
  for y in xs[1:]:x=xor(x,y)
  return x
 clauses.append([parity(list(range(1,n+1)))])
 for i in range(n):clauses.append([-(i+1),parity([1+(i+a)%n for a in A])])
 p=D/'tmp/cyclic.cnf';p.write_text(f'p cnf {nvars} {len(clauses)}\n'+'\n'.join(' '.join(map(str,c))+' 0' for c in clauses)+'\n')
 try:
  r=subprocess.run([solver,'--seed=124',str(p)],capture_output=True,text=True,timeout=.8);s=r.stdout+'\n'+r.stderr;(D/f'outputs/cyclic-{tag}.log').write_text(s)
  return r.returncode
 except subprocess.TimeoutExpired as e:
  (D/f'outputs/cyclic-{tag}.log').write_bytes((e.stdout or b'')+(e.stderr or b''));return 'timeout'
out=[]
for n in [13,45,47,51,53,55,57,59,61]:
 for j in range(25):
  if j==0:A=[1,n-1]
  else:
   k=rng.choice([2,4,6,8,10]);A=sorted(rng.sample(range(1,n),k))
  symmetric=all(n-a in A for a in A);tag=f'{n}-{j}';r=check(n,A,tag);o=dict(n=n,support=A,symmetric=symmetric,solver_returncode=r);out.append(o);print(o,flush=True)
  if r==20 and not symmetric:print('POSSIBLE COUNTEREXAMPLE',o,flush=True)
(D/'outputs/cyclic.json').write_text(json.dumps(out,indent=2))
