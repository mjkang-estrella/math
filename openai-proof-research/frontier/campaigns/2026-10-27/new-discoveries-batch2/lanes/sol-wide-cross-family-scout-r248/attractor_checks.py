import pathlib,json,itertools,random,time
L=pathlib.Path(__file__).resolve().parent
def theta(w,e):return w[::-1].translate(str.maketrans('01','10')) if e else w[::-1]
def close(w,e):
 for k in range(len(w)+1):
  if w[k:]==theta(w[k:],e):return w+theta(w[:k],e)
def masks(w):
 d={};n=len(w)
 for i in range(n):
  for j in range(i+1,n+1):
   s=w[i:j];d[s]=d.get(s,0)|(((1<<(j-i))-1)<<i)
 return list(set(d.values()))
def valid(w,positions):
 m=sum(1<<i for i in set(positions));return all(c&m for c in masks(w))
def four_rule(w):
 out=[]
 for e in [0,1]:
  for a in '01':
   ps=[k for k in range(len(w)) if w[k]==a and w[:k]==theta(w[:k],e)]
   if ps:out.append(max(ps))
 return sorted(set(out))
def solve(cs,k,budget=150000):
 nodes=0;memo=set()
 def go(rows,left):
  nonlocal nodes
  nodes+=1
  if nodes>budget:raise TimeoutError('node cap')
  if not rows:return []
  if left==0:return None
  key=(rows,left)
  if key in memo:return None
  c=min(rows,key=int.bit_count);poss=[i for i in range(c.bit_length()) if c>>i&1]
  poss.sort(key=lambda i:-sum(bool(r>>i&1) for r in rows))
  for i in poss:
   rem=tuple(r for r in rows if not(r>>i&1))
   ans=go(rem,left-1)
   if ans is not None:return [i]+ans
  memo.add(key);return None
 try:return dict(positions=go(tuple(sorted(cs)),k),nodes=nodes,complete=True)
 except TimeoutError:return dict(nodes=nodes,complete=False)
def run():
 words={};level={'':[]}
 for depth in range(1,6):
  nxt={}
  for w,dr in level.items():
   for a,e in itertools.product('01',[0,1]):
    v=close(w+a,e);nxt.setdefault(v,dr+[(a,e)])
  level=nxt
  for w,dr in level.items():words.setdefault(w,dr)
 rng=random.Random(248)
 for _ in range(100):
  w='';dr=[]
  for depth in range(9):
   a=rng.choice('01');e=rng.randrange(2);v=close(w+a,e)
   if len(v)>192:break
   w=v;dr.append((a,e))
  words.setdefault(w,dr)
 result=[];failed_rule=None;start=time.monotonic()
 for w,dr in sorted(words.items(),key=lambda x:len(x[0])):
  if time.monotonic()-start>175:break
  cs=masks(w);rule=four_rule(w)
  if failed_rule is None and not valid(w,rule):failed_rule=dict(word=w,directive=dr,rule=rule)
  ans=solve(cs,4)
  if ans.get('positions') is not None:assert valid(w,ans['positions'])
  result.append(dict(word=w,directive=dr,**ans))
 out=dict(tested=len(result),generated=len(words),max_length=max(len(r['word']) for r in result),naive_rule_failure=failed_rule,rows=result,seconds=time.monotonic()-start)
 (L/'attractor-results.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items() if k!='rows'},indent=2));print('unresolved',sum(not r['complete'] for r in result),'no4',sum(r['complete'] and r['positions'] is None for r in result))
if __name__=='__main__':run()
