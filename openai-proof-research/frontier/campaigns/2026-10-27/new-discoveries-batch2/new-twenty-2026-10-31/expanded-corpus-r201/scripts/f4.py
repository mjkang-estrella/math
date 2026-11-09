import itertools,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];roots=set()
for i in range(4):
 for s in [-2,2]:r=[0]*4;r[i]=s;roots.add(tuple(r))
for i,j in itertools.combinations(range(4),2):
 for s,t in itertools.product([-2,2],repeat=2):r=[0]*4;r[i]=s;r[j]=t;roots.add(tuple(r))
roots.update(itertools.product([-1,1],repeat=4));pos=[]
for x in roots:
 c4=x[0];c1=(x[1]+c4)//2;c2=(x[2]+2*c1+c4)//2;c3=(x[3]+2*c2+c4)//2;c=(c1,c2,c3,c4)
 if min(c)>=0:pos.append(c)
pos.sort(key=lambda c:(sum(c),c));n=len(pos);assert n==24
cmp=lambda a,b:all(x<=y for x,y in zip(a,b)) or all(x>=y for x,y in zip(a,b))
comp=[sum(1<<j for j in range(n) if cmp(pos[i],pos[j])) for i in range(n)];ants=[]
def go(mask,left):
 ants.append(mask)
 while left:
  bit=left&-left;left-=bit;i=bit.bit_length()-1;go(mask|bit,left&~comp[i])
go(0,(1<<n)-1);r=max(map(sum,pos))-1
layers=[[i for i,c in enumerate(pos) if sum(c)-1==h] for h in range(r+1)]
def rv(A):
 for s in range(r+1):
  for h in range(s,r+1):
   for i in layers[h]:
    if A>>i&1:A^=1<<i
    elif not A&comp[i]:A|=1<<i
 return A
assert all(rv(rv(A))==A for A in ants)
fail=[{'A':[pos[i] for i in range(n) if A>>i&1],'Rvac':[pos[i] for i in range(n) if rv(A)>>i&1]} for A in ants if A.bit_count()+rv(A).bit_count()!=4]
out={'positive_roots':pos,'antichains':len(ants),'rowvacuation_involutive':True,'cardinality_duality_failures':fail,'interpretation':'Known failure of the source proposed rowvacuation, not a refutation of existence of another involution.'}
(D/'outputs/f4.json').write_text(json.dumps(out,indent=2));print('antichains',len(ants),'failures',len(fail))
