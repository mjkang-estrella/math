import numpy as np,math,json,time,sys
p=11;q=p**7;N=q-1;rng=np.random.default_rng(346233)
xs=rng.choice(q,(65536 if len(sys.argv)>1 else 8192),replace=False);xps=xs-xs%p+(xs%p+1)%p
vals=np.concatenate([xs,xps]);a=np.array([(vals//(p**j))%p for j in range(7)],dtype=np.int64)
def mul(a,b):
 w=np.zeros((13,a.shape[1]),dtype=np.int64)
 for i in range(7):
  for j in range(7):w[i+j]+=a[i]*b[j]
 w%=p
 for i in range(12,6,-1):w[i-7]=(w[i-7]-4*w[i])%p;w[i-6]=(w[i-6]-w[i])%p
 return w[:7]
pows=[a]
for j in range(24):pows.append(mul(pows[-1],pows[-1]))
base=[1,(p**2+1)//2,(p-1)*p**6+p**5+(p-2)*p**3+(p-1)*p**2+p,(p**4+1)//2,(p**6+1)//2,(p-2)*p**6+(p-2)*p**5+(p-1)*p**4+p**3+p**2+p,(p**7+1)//(p+1)]
known={d*p**j%N for d in base for j in range(7)}
trials=[]
ds=[t['d'] for t in json.load(open('outputs/pcn.json'))['trials'] if t['rejection'] is None] if len(sys.argv)>1 else range(1,2002,2)
for d in ds:
 if d in known:continue
 if math.gcd(d,N)!=1:trials.append({'d':d,'rejection':'a=0 power is not a permutation'});continue
 v=np.zeros_like(a);v[0]=1
 for j in range(d.bit_length()):
  if d>>j&1:v=mul(v,pows[j])
 f=(v[:,:len(xs)]+v[:,len(xs):])%p;enc=sum(f[j]*p**j for j in range(7));order=np.argsort(enc);hits=np.flatnonzero(enc[order][:-1]==enc[order][1:])
 if len(hits):
  h=int(hits[0]);i=int(order[h]);j=int(order[h+1]);trials.append({'d':d,'rejection':'exact sampled a=1 collision','x':int(xs[i]),'y':int(xs[j]),'value':int(enc[i])})
 else:trials.append({'d':d,'rejection':None})
 if d%101==0:print('through d',d,flush=True)
json.dump({'p':p,'extension':7,'modulus':'X^7+X+4; irreducibility checked by sympy gf_irreducible_p before run','distinct_x_samples':len(xs),'trials':trials},open('outputs/pcn-refine.json' if len(sys.argv)>1 else 'outputs/pcn.json','w'),indent=2)
print('trials',len(trials),'survivors',[t['d'] for t in trials if t['rejection'] is None],flush=True)
