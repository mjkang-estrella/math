import sys,json,itertools,pathlib,collections
D=pathlib.Path(sys.argv[1]); mode=sys.argv[2]; N=int(sys.argv[3]); p=D/'outputs'/f'{mode}-{N}'
class CNF:
 def __init__(self,n): self.n=n;self.cs=[];self.zero=self.var();self.cs.append([-self.zero])
 def var(self):self.n+=1;return self.n
 def gate(self,ins,fun):
  o=self.var()
  for vals in itertools.product([False,True],repeat=len(ins)):
   self.cs.append([(-v if x else v) for v,x in zip(ins,vals)]+[o if fun(*vals) else -o])
  return o
 def add(self,a,b):
  c=self.zero;out=[]
  for i in range(max(len(a),len(b))):
   x=a[i] if i<len(a) else self.zero;y=b[i] if i<len(b) else self.zero
   out.append(self.gate([x,y,c],lambda x,y,c:x^y^c));c=self.gate([x,y,c],lambda x,y,c:(x+y+c)>=2)
  return out+[c]
 def count(self,vs):
  rows=[[v] for v in vs]
  while len(rows)>1:rows=[self.add(rows[i],rows[i+1]) if i+1<len(rows) else rows[i] for i in range(0,len(rows),2)]
  return rows[0]
 def eq(self,bits,v):
  for i,x in enumerate(bits):self.cs.append([x if v>>i&1 else -x])
 def le(self,bits,v,guard=[]):
  for i,x in enumerate(bits):
   if not(v>>i&1):self.cs.append(guard+[-x]+[-bits[j] if v>>j&1 else bits[j] for j in range(i+1,len(bits))])
 def write(self,p):p.with_suffix('.cnf').write_text(f'p cnf {self.n} {len(self.cs)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in self.cs));print(p,self.n,len(self.cs),flush=True)
if mode=='cube':
 M=N;N=32;c=CNF(N);c.eq(c.count(list(range(1,33))),M)
 layers=[[x for x in range(N) if x%(1<<i)==1<<(i-1)] for i in range(1,6)]+[[0]]
 fixed=[];opts=[]
 for layer in layers:
  if len(fixed)+len(layer)<M:fixed+=layer;continue
  for sub in itertools.combinations(layer,M-len(fixed)):
   A=set(fixed)|set(sub);opts.append((sum((x+y)%N in A for x in A for y in A),sorted(A)))
  break
 bound,A=min(opts);terms=[];groups=collections.Counter(tuple(sorted({x+1,y+1,(x+y)%N+1})) for x in range(N) for y in range(N))
 for xs,w in groups.items():
  t=c.var();c.cs.extend([[-t,x] for x in xs]);c.cs.append([t]+[-x for x in xs]);terms += [t]*w
 c.le(c.count(terms),bound-1)
 p.with_suffix('.json').write_text(json.dumps(dict(M=M,centred_ST=bound,centred=A,groups=len(groups))))
else:
 c=CNF(N);c.cs.append([1])
 # x_i = +1. Every cascade tail has at most floor(tail_length/2)
 # pluses when root is +1, and at most that many minuses otherwise.
 for d in range(1,N//2+1):
  tail=[];bits=None
  for j in range(2,N//d+1):
   tail.append(d*j)
   if j==2:bits=[2*d];c.cs.extend([[-d,-2*d],[d,2*d]])
   else:
    bits=c.add(bits or [],[d*j])[:(j).bit_length()];c.le(bits,(j-1)//2,[-d]);c.le([-x for x in bits], (1<<len(bits))-1-((j)//2),[d])
 c.write(p);sys.exit()
c.write(p)
