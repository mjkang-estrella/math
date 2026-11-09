from pathlib import Path
import functools,json,random,time
L=Path(__file__).resolve().parent
def children(w):
 return sorted({w[:i]+w[i+k:] for k in range(1,len(w)//2+1) for i in range(len(w)-2*k+1) if w[i:i+k]==w[i+k:i+2*k]})
def roots(w):
 seen={}; todo=[(w,False)]
 while todo:
  v,done=todo.pop()
  if v in seen:continue
  ch=children(v)
  if done or not ch:
   seen[v]=frozenset().union(*(seen[c] for c in ch)) if ch else frozenset([v])
  else:
   todo.append((v,True));todo.extend((c,False) for c in ch if c not in seen)
  if len(seen)>40000:raise RuntimeError('40000-state diagnostic cap')
 return seen[w],seen
if __name__=='__main__':
 rng=random.Random(250);start=time.monotonic();base='abcbabcbcacbcacabacabcbacabcabacacbcacbabcbcacbca'
 r,s=roots(base);print('source81',len(r),'states',len(s),flush=True)
 best=base;score=abs(len(r)-80);log=[];w=base
 for it in range(1800):
  if time.monotonic()-start>125:break
  if it%10==0:w=base
  cand=w
  op=rng.randrange(4);i=rng.randrange(len(w))
  if op==0:cand=w[:i]+rng.choice('abc')+w[i+1:]
  elif op==1 and len(w)<60:cand=w[:i]+rng.choice('abc')+w[i:]
  elif op==2:cand=w[:i]+w[i+1:]
  else:
   k=rng.randrange(1,min(5,len(w)-i)+1);cand=w[:i]+w[i:i+k]+w[i:]
  try:rr,ss=roots(cand)
  except RuntimeError:continue
  sc=abs(len(rr)-80)
  if sc<score:best=cand;score=sc;print('best',it,len(rr),cand,flush=True)
  if sc<=abs(len(roots(w)[0])-80) or rng.random()<.06:w=cand
  log.append({'iteration':it,'length':len(cand),'count':len(rr),'states':len(ss)})
  if len(rr)==80:
   (L/'witness.json').write_text(json.dumps({'word':cand,'roots':sorted(rr),'dag':{v:children(v) for v in ss}},indent=2));break
 (L/'diagnostics.json').write_text(json.dumps({'trials':log,'best_word':best,'distance_to80':score,'wall':time.monotonic()-start},indent=2))
