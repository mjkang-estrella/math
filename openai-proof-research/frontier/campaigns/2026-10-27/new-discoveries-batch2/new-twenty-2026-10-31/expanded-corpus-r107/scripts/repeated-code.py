import pathlib,json,itertools
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for q,mod in [(2,3),(4,7),(8,11),(16,19),(32,37),(64,67)]:
 def mul(a,b):
  v=0
  while b:
   if b&1:v^=a
   b>>=1;a<<=1
   if a&q:a^=mod
  return v
 table=[[mul(a,b) for b in range(q)] for a in range(q)]
 assert all(len(set(table[a]))==q for a in range(1,q))
 for s in ([1,2] if q<=32 else [1]):
  vs=list(itertools.product(range(q),repeat=s));weights=set()
  for v in vs[1:]:
   if s==1:w=sum(table[v[0]][x[0]]!=0 for x in vs[1:])
   else:w=sum((table[v[0]][x[0]]^table[v[1]][x[1]])!=0 for x in vs[1:])
   weights.add(w)
  row={'q':q,'support_dimension':s,'all_support_messages_tested':len(vs),'length':q**s-1,'weights':sorted(weights),'predicted':(q-1)*q**(s-1),'matches':weights=={(q-1)*q**(s-1)}};print(row,flush=True);out.append(row)
(D/'outputs/repeated-code.json').write_text(json.dumps(out,indent=2)+'\n')
