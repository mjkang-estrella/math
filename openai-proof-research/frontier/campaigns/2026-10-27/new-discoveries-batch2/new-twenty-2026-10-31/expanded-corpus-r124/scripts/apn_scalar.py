import pathlib,json,collections
D=pathlib.Path(__file__).resolve().parents[1];q=128;pol=0x83

def mul(a,b):
 r=0
 while b:
  if b&1:r^=a
  b>>=1;a<<=1
  if a&q:a^=pol
 return r

def pw(a,e):
 r=1
 while e:
  if e&1:r=mul(r,a)
  a=mul(a,a);e>>=1
 return r
assert all(mul(a,pw(a,q-2))==1 for a in range(1,q))
B=sorted({pw(x,39)^pw(x^1,39) for x in range(q)})
blocks=set()
for a in range(1,q):
 A=[mul(a,x) for x in B]
 for b in range(q):blocks.add(sum(1<<(x^b) for x in A))
counts=[sum((v&3)==3 and ((v>>t)&1) for v in blocks) for t in range(2,q)]
o=dict(n=7,s=39,modulus=pol,block=B,distinct_blocks=len(blocks),min=min(counts),max=max(counts),min_t=2+counts.index(min(counts)),max_t=2+counts.index(max(counts)),triple_01t_counts=counts);(D/'outputs/apn-scalar.json').write_text(json.dumps(o,indent=2));print(o)
