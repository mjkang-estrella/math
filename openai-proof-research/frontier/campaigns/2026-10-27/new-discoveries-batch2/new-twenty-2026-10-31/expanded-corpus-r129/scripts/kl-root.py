import itertools,json
# Diagnostic standard-representation root-basis model; semantic KL identification is not certified.
for n in range(4,10):
 good=sep=bad=0;examples=[]
 for p in itertools.permutations(range(n)):
  cols=[set(range(min(p[i],p[i+1]),max(p[i],p[i+1]))) for i in range(n-1)]
  left=list(range(n-1));rows=set(range(n-1));ok=True
  while left:
   q=next((j for j in left if len(cols[j]&rows)==1),None)
   if q is None:ok=False;break
   r=next(iter(cols[q]&rows));rows.remove(r);left.remove(q)
  s=not any((p[a]<p[c]<p[b]<p[d] or p[c]<p[a]<p[d]<p[b]) for a,b,c,d in []) if False else None
  # rank patterns 2413,3142
  s=not any((p[c]<p[a]<p[d]<p[b] or p[b]<p[d]<p[a]<p[c]) for a,b,c,d in itertools.combinations(range(n),4))
  good+=ok;sep+=s
  if ok!=s:
   bad+=1
   if len(examples)<3:examples.append(p)
 print(json.dumps({'n':n,'permutations':__import__('math').factorial(n),'triangularizable':good,'separable':sep,'mismatch':bad,'examples':examples}),flush=True)
