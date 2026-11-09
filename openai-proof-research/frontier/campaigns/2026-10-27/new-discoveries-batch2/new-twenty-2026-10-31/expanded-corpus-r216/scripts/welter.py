from itertools import combinations
import sys
N=int(sys.argv[1]);K=int(sys.argv[2]);g={():0};counts={}
for k in range(1,K+1):
 for top in range(N+1):
  for pre in combinations(range(top),k-1):
   s=pre+(top,);used=set(pre);vals=set()
   for x in range(top):
    if x not in used:vals.add(g[tuple(sorted(pre+(x,)))])
   z=0
   while z in vals:z+=1
   g[s]=z
 counts[k]=sum(1 for s in g if len(s)==k)
 print('coins',k,'states',counts[k],flush=True)
for k in range(2,K+1):
 for m in range(1,13):
  if (k-1)*m>N-4*m:continue
  seq=[g[tuple(a+j*m for j in range(k))] for a in range(N-(k-1)*m+1)]
  bad=[a for a in range(len(seq)-2*m) if seq[a]!=seq[a+2*m]]
  print('AP coins',k,'m',m,'terms',len(seq),'last mismatch',max(bad,default=-1),'tail',seq[-2*m:],flush=True)
print('Finite recurrence data do not prove ultimate periodicity or its failure.')
