import sys,pathlib,json,hashlib,itertools,random,collections
D=pathlib.Path(sys.argv[1]);mode=sys.argv[2];stem=sys.argv[3];p=D/'outputs'/stem
cs=[]
for line in p.with_suffix('.cnf').open():
 if line.startswith(('p','c')):continue
 cs.append(list(map(int,line.split()))[:-1])
if mode=='lrat':
 adds={};last=None
 for line in p.with_suffix('.lrat').open():
  a=line.split()
  if not a or a[1]=='d':continue
  a=list(map(int,a));z=a.index(0);adds[a[0]]=(a[1:z],a[z+1:-1]);last=a[0]
 assert last and adds[last][0]==[],'no final empty clause'
 need={last};todo=[last]
 while todo:
  i=todo.pop()
  for h in adds[i][1]:
   assert h>0,'RAT hints unsupported'
   if h>len(cs) and h not in need:need.add(h);todo.append(h)
 db={i+1:c for i,c in enumerate(cs)};out=[]
 for i in sorted(need):
  clause,hints=adds[i];vals={}
  for lit in clause:
   v=abs(lit);b=lit<0
   assert v not in vals or vals[v]==b,'tautology unsupported'
   vals[v]=b
  conflict=False
  for h in hints:
   assert h in db and h<i
   r=db[h];free=[];sat=False
   for x in r:
    if abs(x) not in vals:free.append(x)
    elif vals[abs(x)]==(x>0):sat=True;break
   assert not sat,('satisfied hint',i,h)
   free=list(set(free))
   if not free:conflict=True;break
   assert len(free)==1,('not unit',i,h,len(free))
   x=free[0];vals[abs(x)]=x>0
  assert conflict,('no RUP conflict',i)
  db[i]=clause;out.append(' '.join(map(str,[i]+clause+[0]+hints+[0]))+'\n')
 target=p.with_suffix('.trim.lrat');target.write_text(''.join(out));r=dict(original_additions=len(adds),trim_additions=len(need),trim_bytes=target.stat().st_size,sha256=hashlib.sha256(target.read_bytes()).hexdigest(),RUP_verified=True)
 p.with_suffix('.check.json').write_text(json.dumps(r,indent=2));print(r)
elif mode=='model':
 vals={}
 for line in (D/'logs'/f'{stem}.log').open():
  if line.startswith('v '):
   for x in map(int,line.split()[1:]):
    if x:vals[abs(x)]=x>0
 assert all(any(vals.get(abs(x))==(x>0) for x in c) for c in cs)
 N=int(stem.split('-')[-1]);f=[1 if vals[i] else -1 for i in range(1,N+1)]
 checks=0
 for d in range(1,N+1):
  tail=0
  for j in range(2,N//d+1):
   tail+=f[d*j-1];assert f[d-1]*tail<=0,(d,j);checks+=1
 r=dict(N=N,checks=checks,verified=True,colors=f);p.with_suffix('.witness.json').write_text(json.dumps(r));print(dict(N=N,checks=checks,verified=True))
elif mode=='test':
 # Generic CNF unit propagation with complete primary inputs. No circuit code imported.
 rng=random.Random(9851);N=32 if stem.startswith('cube') else int(stem.split('-')[-1]);trials=20
 watch=collections.defaultdict(list)
 for i,c in enumerate(cs):
  for x in c:watch[abs(x)].append(i)
 def propagate(primary):
  vals=dict(primary);q=collections.deque(range(len(cs)));inq=set(q)
  while q:
   i=q.popleft();inq.discard(i);c=cs[i]
   if any(abs(x) in vals and vals[abs(x)]==(x>0) for x in c):continue
   free=[x for x in c if abs(x) not in vals]
   if not free:return False
   if len(free)==1:
    x=free[0];vals[abs(x)]=x>0
    for k in watch[abs(x)]:
     if k not in inq:q.append(k);inq.add(k)
  assert len(vals)==max(watch),'unforced circuit variables'
  return True
 for z in range(trials):
  if stem.startswith('cube'):
   M=int(stem.split('-')[1]);A=set(rng.sample(range(32),M if z%2 else rng.randrange(33)));primary={i+1:i in A for i in range(32)}
   bound=json.loads(p.with_suffix('.json').read_text())['centred_ST'];expected=len(A)==M and sum((x+y)%32 in A for x in A for y in A)<bound
  else:
   f=[rng.choice([-1,1]) for _ in range(N)];primary={i+1:f[i]==1 for i in range(N)}
   expected=f[0]==1 and all(f[d-1]*sum(f[d*j-1] for j in range(2,k+1))<=0 for d in range(1,N+1) for k in range(2,N//d+1))
  assert propagate(primary)==expected,z
 print('independent truth tests passed',trials,stem)
