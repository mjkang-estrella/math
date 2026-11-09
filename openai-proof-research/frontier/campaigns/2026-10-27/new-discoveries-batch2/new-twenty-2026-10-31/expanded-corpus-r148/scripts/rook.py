import itertools,json,pathlib,sys,time
L=pathlib.Path(__file__).resolve().parents[1];p=65521;out=[]
def comps(n,d):
 if d==1:yield (n,);return
 for a in range(n+1):
  for v in comps(n-a,d-1):yield (a,)+v
for d,n in [(7,3),(7,4),(7,5),(7,6),(8,3),(8,4),(8,5),(9,4)]:
 vs=list(comps(n,d));N=len(vs);index={v:i for i,v in enumerate(vs)};basis={}
 for i,v in enumerate(vs):
  row={i:n}
  for a in range(d):
   for b in range(a+1,d):
    s=v[a]+v[b]
    for x in range(s+1):
     if x==v[a]:continue
     w=list(v);w[a]=x;w[b]=s-x;row[index[tuple(w)]]=1
  while row:
   lead=min(row);r=row[lead]
   if lead not in basis:
    inv=pow(r,-1,p);basis[lead]={j:c*inv%p for j,c in row.items()};break
   for j,c in basis[lead].items():
    z=(row.get(j,0)-r*c)%p
    if z:row[j]=z
    elif j in row:del row[j]
 mah=[1]
 for j in range(1,d+1):
  new=[0]*(len(mah)+j-1)
  for a,x in enumerate(mah):
   for b in range(j):new[a+b]+=x
  mah=new
 rec={'d':d,'n':n,'vertices':N,'prime':p,'nullity':N-len(basis),'mahonian':mah[n]};out.append(rec);print(rec,flush=True);(L/'outputs/rook.json').write_text(json.dumps(out,indent=2))
