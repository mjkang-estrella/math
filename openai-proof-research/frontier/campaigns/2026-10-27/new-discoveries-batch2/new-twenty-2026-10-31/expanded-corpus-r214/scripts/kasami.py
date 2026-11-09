import pathlib,json,math,collections,hashlib
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for n,poly in [(5,0x25),(7,0x83),(9,0x211)]:
 q=1<<n
 def mul(a,b):
  z=0
  while b:
   if b&1:z^=a
   a<<=1
   if a&q:a^=poly
   b>>=1
  return z
 def power(a,e):
  z=1
  while e:
   if e&1:z=mul(z,a)
   a=mul(a,a);e>>=1
  return z
 assert len({power(2,e) for e in range(q-1)})==q-1
 perms=[[x^(1<<j) for x in range(q)] for j in range(n)]+[[mul(2,x) for x in range(q)]]
 for i in range(1,(n-1)//2+1):
  if math.gcd(i,n)>1:continue
  s=2**(2*i)-2**i+1;inv=pow(2**i+1,-1,q-1)
  image={power(power(x^1,s)^power(x,s)^1,inv) for x in range(q)}
  block=set(range(q))-image;assert len(block)==q//2
  v=sum(1<<x for x in block);basis={};todo=collections.deque([v])
  while todo:
   b=todo.popleft()
   while b:
    j=b.bit_length()-1
    if j in basis:b^=basis[j]
    else:break
   if not b:continue
   basis[b.bit_length()-1]=b
   for perm in perms:
    z=b;w=0
    while z:
     low=z&-z;x=low.bit_length()-1;w|=1<<perm[x];z-=low
    todo.append(w)
  row={'n':n,'i':i,'primitive_polynomial_bits':poly,'base_block':sorted(block),'dimension':len(basis),'basis':[str(b) for b in basis.values()]};out.append(row);print(n,i,len(basis),flush=True)
(D/'outputs/kasami9.json').write_text(json.dumps(out,indent=2))
