import random,sys,math,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];k=int(sys.argv[1]);steps=int(sys.argv[2]);rng=random.Random(128+k)
def dyck(a=0,b=0,w=()):
 if b==k:yield w;return
 if a<k:yield from dyck(a+1,b,w+(1,))
 if b<a:yield from dyck(a,b+1,w+(0,))
words=list(dyck());n=2*k+1
perms=[];groups=[]
for w in words:
 hi=list(range(1,k+1));lo=list(range(k+1,n));rng.shuffle(hi);rng.shuffle(lo);perms.append([0]+[hi.pop()if x else lo.pop()for x in w]);groups.append([[j+1 for j,x in enumerate(w)if x==v]for v in (0,1)])
def edges(p):return [sum(1<<p[(i+j)%n] for j in range(k))for i in range(n)]
sets=[edges(p)for p in perms];counts=[0]*(1<<n)
for es in sets:
 for e in es:counts[e]+=1
energy=sum(max(0,v-1)for v in counts);best=energy
for t in range(steps):
 i=rng.randrange(len(perms));g=rng.choice(groups[i]);a,b=rng.sample(g,2);p=perms[i];old=sets[i];before=energy
 for e in old:
  if counts[e]>1:energy-=1
  counts[e]-=1
 p[a],p[b]=p[b],p[a];new=edges(p)
 for e in new:
  if counts[e]:energy+=1
  counts[e]+=1
 temp=max(.08,1.5*(1-(t%50000)/50000))
 if energy<=before or rng.random()<math.exp((before-energy)/temp):sets[i]=new
 else:
  for e in new:counts[e]-=1
  for e in old:counts[e]+=1
  p[a],p[b]=p[b],p[a];energy=before
 if energy<best:
  best=energy
  if best<10 or best%10==0:print('step',t,'best duplicate excess',best,flush=True)
  (D/f'outputs/wreath-k{k}-best.json').write_text(json.dumps(dict(k=k,steps=t+1,excess=best,permutations=perms))+'\n')
 if best==0:break
print(dict(k=k,dyck_words=len(words),steps=t+1,best_excess=best,total_subsets=math.comb(n,k),seed=128+k,coverage='stochastic constrained permutations; no exhaustive nonexistence'),flush=True)
