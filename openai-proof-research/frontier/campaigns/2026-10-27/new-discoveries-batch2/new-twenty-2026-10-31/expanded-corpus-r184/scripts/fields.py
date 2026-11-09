import pathlib,json,sys
D=pathlib.Path(__file__).resolve().parents[1];m=int(sys.argv[1]);q=1<<m;mod={5:0b100101,7:0b10000011,9:0b1000010001,11:0b100000000101}[m]
def mul(a,b):
 c=0
 while b:
  if b&1:c^=a
  a<<=1;b>>=1
  if a&q:a^=mod
 return c
def power(a,b):
 c=1
 while b:
  if b&1:c=mul(c,a)
  a=mul(a,a);b>>=1
 return c
# Verify field representation rather than assuming irreducibility.
assert all(power(x,q-1)==1 for x in range(1,q))
M=[[mul(a,b) for b in range(q)] for a in range(q)]
out=[]
for kind,exps in [('translation',[2]),('Segre',[6]),('Cherowitzo',[1<<((m+1)//2),(1<<((m+1)//2))+2,3*(1<<((m+1)//2))+4])]:
 f=[]
 for x in range(q):
  y=0
  for e in exps:y^=power(x,e)
  f.append(y)
 assert len(set(f))==q
 images=[]
 for b in range(1,q):
  s=set(f[x]^M[b][x] for x in range(q));assert len(s)==q//2;images.append(s)
 blocks=set()
 for s in images:
  for c in range(q):blocks.add(sum(1<<(x^c) for x in s))
 r={'kind':kind,'m':m,'q':q,'ordinary_blocks':len(blocks),'expected':2*(q-1) if kind=='translation' else q*(q-1),'exponents':exps}
 if m<=7 and kind=='Cherowitzo':
  blocks=set()
  for a in range(1,q):
   for s in images:
    t=[M[a][x] for x in s]
    for c in range(q):blocks.add(sum(1<<(x^c) for x in t))
  r['extended_blocks']=len(blocks);r['extended_expected']=q*(q-1)**2
 out.append(r);print(json.dumps(r),flush=True)
 (D/'outputs'/f'fields-{m}.json').write_text(json.dumps(out,indent=2))
