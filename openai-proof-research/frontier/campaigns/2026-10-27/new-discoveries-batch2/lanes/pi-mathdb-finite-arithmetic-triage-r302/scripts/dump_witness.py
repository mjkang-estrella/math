import json,time
def evper(seq):
    n=len(seq)
    for p in range(1,n):
        if all(seq[i]==seq[i+p] for i in range(n-p)): return p
    return None
def nim(S,N=600):
    g=[0]*(N+1)
    for n in range(1,N+1):
        s={g[n-m] for m in S if m<=n}
        i=0
        while i in s: i+=1
        g[n]=i
    return g
w=[]
for a in range(1,7):
  for b in range(a+1,11):
    for c in range(b+1,15):
      if c==a+b: continue
      g=nim((a,b,c)); t=g[300:]; pg=evper(t)
      if pg not in (a+b,b+c,c+a):
          w.append({"S":[a,b,c],"eventual_period":pg,"claimed_set":[a+b,b+c,c+a],
                    "nim_tail_g600_620":g[600-20:600]})
d={"conjecture_record":375237,"computed_utc":time.strftime("%Y-%m-%dT%H:%M:%SZ",time.gmtime()),
   "method":"nim-values by mex; eventual period = minimal p with full tail p-periodic (tail g[300:600]); claim: period in {a+b,b+c,c+a}, c!=a+b",
   "witness_count":len(w),"witnesses_first_40":w[:40],
   "primary_witness":{"S":[1,3,5],"g_1_40":nim((1,3,5))[1:41]}}
json.dump(d,open('screening/witness-375237.json','w'),indent=1)
print("witnesses:",len(w)); print(json.dumps(d["primary_witness"]["g_1_40"]))
