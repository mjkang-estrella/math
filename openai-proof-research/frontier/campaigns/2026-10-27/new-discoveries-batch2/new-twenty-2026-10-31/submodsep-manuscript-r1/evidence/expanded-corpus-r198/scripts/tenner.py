import pathlib,sys,json,math,collections
D=pathlib.Path(__file__).resolve().parents[1]
def phi(p,m):
 out=collections.Counter()
 for a,b in p:
  k=0
  while a%m==0:a//=m;k+=1
  l=0
  while b:
   out[a*m**l]+=(b%m)*m**k;b//=m;l+=1
 return tuple(sorted((a,b) for a,b in out.items() if b))
def parts(n,hi=None):
 if n==0:yield ();return
 for a in range(min(n,hi or n),1-1,-1):
  for q in parts(n-a,a):yield (a,)+q
def typ(p,s,t):return all(a%s!=0 and b<t for a,b in p)
coverage=[];mx=(0,None);bad=[]
for n in range(1,31):
 count=0
 for raw in parts(n):
  p=tuple(sorted(collections.Counter(raw).items()))
  for s in range(2,11):
   for t in range(2,11):
    if math.gcd(s,t)==1 or not typ(p,s,t):continue
    count+=1;q=p;seen={p};steps=0
    while True:
     q=phi(phi(q,t),s);steps+=1
     if typ(q,t,s):break
     if typ(q,s,t) or q in seen:
      bad.append({'n':n,'s':s,'t':t,'p':p,'q':q,'steps':steps});break
     seen.add(q)
    if steps>mx[0]:mx=(steps,{'n':n,'s':s,'t':t,'p':p})
    if bad:break
   if bad:break
  if bad:break
 coverage.append({'n':n,'eligible_starts':count});print(coverage[-1],flush=True)
 if bad:break
(D/'outputs/tenner-search.json').write_text(json.dumps({'coverage':coverage,'max_steps':mx,'failures':bad},indent=2))
