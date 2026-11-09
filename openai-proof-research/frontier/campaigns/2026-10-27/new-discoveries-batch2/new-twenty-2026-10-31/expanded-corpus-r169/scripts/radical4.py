import pathlib,sys,itertools,math,time,json
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D/'scripts'));from radical import rank
# Importing radical also repeats its short three-root sweep, under the same wrapper.
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
def cols(perms,t):
 out=[]
 for a,b,c,d in perms:
  u=[math.comb(b,j)*(-1)**(b-j) for j in range(b+1)];v=[math.comb(c,j)*(-t)**(c-j) for j in range(c+1)];out.append([0]*a+mul(u,v))
 return out
start=time.monotonic();out={'scope':'Four roots 0,1,t,infinity; normalized min part1; other parts<=14 until100s; exact ranks at t=2,3,5; multi-point diagnostics not universal proof','tested':0,'last':None,'leads':[],'accidental_t2':0}
for a in range(1,15):
 for b in range(1,a+1):
  for c in range(1,b+1):
   if time.monotonic()-start>95:break
   mu=(a,b,c,1);perms=list(set(itertools.permutations(mu)));criterion=False
   for A in itertools.product(set(mu),repeat=4):
    count=sum(all(p[j]>=A[j] for j in range(4)) for p in perms)
    if count>=2 and count>=sum(mu)-sum(A)+2:criterion=True;break
   out['tested']+=1;out['last']=mu
   if criterion:continue
   if rank(cols(perms,2))<len(perms):
    if rank(cols(perms,3))<len(perms) and rank(cols(perms,5))<len(perms):out['leads'].append({'mu':mu,'perms':len(perms)})
    else:out['accidental_t2']+=1
  if time.monotonic()-start>95:break
 if time.monotonic()-start>95:break
out['wall_seconds']=time.monotonic()-start;(D/'outputs/radical4.json').write_text(json.dumps(out,indent=2));print(out)
