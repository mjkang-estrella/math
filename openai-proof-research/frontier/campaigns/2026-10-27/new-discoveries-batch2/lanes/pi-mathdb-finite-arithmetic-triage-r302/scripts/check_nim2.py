def evper(seq):
    n=len(seq)
    for p in range(1,n):
        ok=True
        for i in range(n-p):
            if seq[i]!=seq[i+p]: ok=False;break
        if ok: return p
    return None
def nim(S,N=3000):
    g=[0]*(N+1)
    for n in range(1,N+1):
        s={g[n-m] for m in S if m<=n}
        i=0
        while i in s: i+=1
        g[n]=i
    return g
bad1=[];bad2=[]
for a in range(1,7):
  for b in range(a+1,11):
    for c in range(b+1,15):
      g=nim((a,b,c),3000)
      tail=g[2000:]; V=[0 if x==0 else 1 for x in tail]
      pg,pv=evper(tail),evper(V)
      if pg!=pv: bad1.append(((a,b,c),pg,pv))
      if c!=a+b and pg not in (a+b,b+c,c+a): bad2.append(((a,b,c),pg))
print("323014 violations:",bad1[:12],"count",len(bad1))
print("375237 violations:",bad2[:12],"count",len(bad2))
# also 2-element and 1-element
b1=[]
for a in range(1,15):
  g=nim((a,),3000); t=g[2000:]; V=[0 if x else 1 for x in t]
  if evper(t)!=evper(V): b1.append((a,evper(t),evper(V)))
for a in range(1,10):
  for b in range(a+1,15):
    g=nim((a,b),3000); t=g[2000:]; V=[0 if x else 1 for x in t]
    if evper(t)!=evper(V): b1.append(((a,b),evper(t),evper(V)))
print("323014 violations for <=2 element sets:",b1[:10],"count",len(b1))
# sample: verify (1,2,4) explicitly
g=nim((1,2,4),30); print("g(1..29) S=(1,2,4):",g[1:30])
