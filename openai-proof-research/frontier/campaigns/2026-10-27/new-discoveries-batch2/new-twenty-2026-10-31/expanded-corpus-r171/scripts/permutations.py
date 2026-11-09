import itertools,math,pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];out=[]
def pattern(v):return tuple(sorted(v).index(i)+1 for i in v)
for n in range(1,9):
 counts={k:{p:0 for p in itertools.permutations(range(1,k+1))} for k in range(3,min(6,n)+1)}
 for perm in itertools.permutations(range(n)):
  for k,d in counts.items():
   for p in {pattern(v) for v in itertools.combinations(perm,k)}:d[p]+=1
 rows=[]
 for k,d in counts.items():
  M={3:(2,1,3),4:(1,3,2,4),5:(2,1,4,3,5),6:(1,3,2,5,4,6)}[k]
  avoids={p:math.factorial(n)-v for p,v in d.items()};maximum=max(avoids.values())
  rows.append(dict(k=k,patterns=len(d),M=M,M_avoidance=avoids[M],maximum=maximum,failures=[list(p) for p,v in avoids.items() if v>avoids[M]]))
 out.append(dict(n=n,permutations=math.factorial(n),rows=rows));(D/'outputs/permutations.json').write_text(json.dumps(out,indent=2)+'\n');print(n,rows,flush=True)
