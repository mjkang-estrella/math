from work import *
N=2**19
u=bytearray(N);u[1]=1
for n in range(3,N,2):u[n]=u[(n-3)//4] if n%4==3 else u[(n-3)//2]
a=[n for n,x in enumerate(u) if x];b=[n for n,x in enumerate(u) if not x]
g=[b[i+1]-b[i] for i in range(len(b)-1)]
c=[x-j-1 for j,x in enumerate(a)]
assert set(g)=={1,2};assert [i for i,x in enumerate(g) if x==2]==[x for x in c if x<len(g)]
v=u[1::2];image=[x for bit in v for x in ([2] if bit else [1,1])];assert image[:len(g)]==g
trans={'S':'S2','2':'34','3':'56','4':'32','5':'35','6':'87','7':'86','8':'88'}
word='S'
for _ in range(19):word=''.join(trans[x] for x in word)
assert [int(x in '26') for x in word]==list(u)
# Gaps are a NONuniform nonerasing morphic image of a 2-uniform fixed point.
gapcode={q:([2] if trans[q][1] in '26' else [1,1]) for q in trans}
mg=[x for q in word for x in gapcode[q]];assert mg[:len(g)]==g
# Exact two-sided truncated composition check in F2, independently from recurrence.
M=192;mask=(1<<M)-1
def mul(x,y):
 z=0
 while y:
  bit=y&-y;z^=x<<(bit.bit_length()-1);y-=bit
 return z&mask
def compose(coeff,arg):
 out=0;power=1
 for bit in coeff:
  if bit:out^=power
  power=mul(power,arg)
 return out
d=[((n+1)&-(n+1)).bit_length()%2 ^ 1 for n in range(M)]
di=sum(x<<i for i,x in enumerate(d));ui=sum(u[i]<<i for i in range(M))
assert compose(d,ui)==2==compose(u[:M],di)
diag={}
for k in [2,3,4,5,7,8]:
 rows=[]
 for e in range(5):
  step=k**e
  if step*128>len(g):break
  rows.append({'depth':e,'distinct_prefixes_128':len({bytes(g[r:r+step*128:step]) for r in range(step)})})
 diag[k]=rows
# Earliest new gap lengths between exceptional gap positions.
records=[];seen=set()
for j in range(len(c)-1):
 dist=c[j+1]-c[j]
 if dist not in seen:seen.add(dist);records.append({'distance':dist,'j':j,'c_j':c[j],'a_j':a[j]})
F=[0,1]
for _ in range(23):F.append(F[-1]+F[-2])
for rec in records:
 for t in range(3,17):
  if rec['a_j']==5*2**t-3:
   assert rec['j']==2*F[t+2]-2
   assert rec['c_j']==5*2**t-2*F[t+2]-2
   assert rec['distance']==2**t+(1 if t%2==0 else 3)
rank=0
for t,bit in enumerate(v):
 assert b[rank]==2*t
 if not bit:assert b[rank+1]==2*t+1
 rank+=2-bit
assert b[2]!=2*b[1]
dump('checks-result.json',{'N':N,'composition_terms':M,'all_assertions_pass':True,'gapcode':gapcode,'kernel_diagnostics_only':diag,'first_new_c_distances':records,'b_prefix':b[:40],'gap_prefix':g[:60]})
print(json.dumps(json.loads((L/'checks-result.json').read_text()),indent=2))
