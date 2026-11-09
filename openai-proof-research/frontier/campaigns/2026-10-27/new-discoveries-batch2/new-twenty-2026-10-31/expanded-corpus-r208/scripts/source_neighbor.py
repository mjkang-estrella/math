import pathlib,json,itertools
D=pathlib.Path(__file__).resolve().parents[1]
def balls(n,e):
 b=[1<<i for i in range(n)];s=set(b)
 for i,j in e:b[i]|=1<<j;b[j]|=1<<i;s.add(b[i]);s.add(b[j])
 return s
source=[(4,5),(3,4),(2,3),(1,2),(0,1),(0,5),(1,5),(0,4),(3,5),(2,4),(1,3),(0,2),(2,5),(1,4),(0,3)]
r=[]
for i,j in itertools.combinations(range(15),2):
 e=source[:];e[i],e[j]=e[j],e[i];v=len(balls(6,e))
 if v>29:r.append(dict(swapped_ranks=[i+1,j+1],count=v))
print(json.dumps(dict(source_count=len(balls(6,source)),improving_swaps=r),indent=2))
