# Capped search: unions S = A ∪ B of two integer APs; report any S with |S+S| > |S-S|.
# A = {d*i : 0<=i<k} (translate/scale WLOG A starts at 0), B = {b + e*j : 0<=j<l}.
# Sum/difference set sizes are translation-invariant and invariant under S -> -S, so WLOG min A = 0.
import sys, time, json
DMAX=int(sys.argv[1]); LMAX=int(sys.argv[2]); BMAX=int(sys.argv[3])
def sizes(elems):
    m=min(elems); el=[x-m for x in elems]; M=0
    for x in el: M|=1<<x
    top=max(el); R=0
    for x in el: R|=1<<(top-x)
    s=0; df=0
    for x in el: s|=M<<x; df|=R<<x
    return bin(s).count('1'), bin(df).count('1')
best=None; bestn=None; cnt=0; found=[]; t=time.time(); seen=set()
for d in range(1,DMAX+1):
  for e in range(d,DMAX+1):
    for k in range(1,LMAX+1):
      A=[d*i for i in range(k)]
      for l in range(1,LMAX+1):
        for b in range(-BMAX,BMAX+1):
          S=frozenset(A+[b+e*j for j in range(l)])
          if len(S)<8: continue
          m=min(S); key=tuple(sorted(x-m for x in S))
          if key in seen: continue
          seen.add(key); cnt+=1
          ps,pd=sizes(key)
          gap=ps-pd
          isap=len(set(key[i+1]-key[i] for i in range(len(key)-1)))==1
          if best is None or gap>best[0]: best=(gap,key,(d,k,b,e,l))
          if not isap and (bestn is None or gap>bestn[0]): bestn=(gap,key,(d,k,b,e,l))
          if gap>0: found.append((key,(d,k,b,e,l),ps,pd))
print(json.dumps({'DMAX':DMAX,'LMAX':LMAX,'BMAX':BMAX,'distinct_sets':cnt,'best_gap':best[0],'best_set':best[1],'best_params':best[2],'best_nonAP_gap':bestn[0],'best_nonAP_set':bestn[1],'best_nonAP_params':bestn[2],'num_sum_dominant':len(found),'examples':found[:5],'secs':time.time()-t}))
