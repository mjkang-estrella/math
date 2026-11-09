import pathlib,json,functools
L=pathlib.Path(__file__).resolve().parents[1]
exec((L/'scripts/delta.py').read_text().split('out=[]')[0])
G=random_cubic(18,1800);A=[[2*int(j in G[i]) for j in range(18)] for i in range(18)]
@functools.lru_cache(None)
def pure(T):
 A=list(map(list,T));W=wyes(A)
 if not W:return len(A),(T,)
 R=[pure(tuple(map(tuple,red(A,x)))) for x in W];b=min(v[0] for v in R)
 return b,tuple(sorted(set(t for v in R if v[0]==b for t in v[1])))
b,starts=pure(tuple(map(tuple,A)));out=[]
for B in starts:
 ends=[i for i,r in enumerate(B) if sorted(v for v in r if v)==[1,1,2,2]]
 chains=[(i,j,k) for i,j in itertools.combinations(ends,2) for k in range(len(B)) if k not in (i,j) and B[i][j]==B[i][k]==B[j][k]==1]
 out.append({'matrix':B,'one_triangle_chains':chains})
print('pure states',len(starts),'min order',b,'with chain1',sum(bool(x['one_triangle_chains']) for x in out))
(L/'outputs/delta-witness.json').write_text(json.dumps(out,indent=2))
