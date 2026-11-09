from pathlib import Path
import json,sys
L=Path(__file__).resolve().parents[1];N=int(sys.argv[1]);a=[0]*(N+1);a[0]=1;distinct=a.copy()
# multiply by (1+2q^k)/(1+q^k), using (1+q^k)new=(1+2q^k)old
for k in range(1,N+1):
 old=a.copy()
 for n in range(k,N+1):a[n]=old[n]+2*old[n-k]-a[n-k]
 for n in range(N,k-1,-1):distinct[n]+=distinct[n-k]
bad=[n for n in range(11,N+1) if a[n]>=distinct[n]]
print(json.dumps({'N':N,'bad':bad,'min_gap':min((distinct[n]-a[n],n) for n in range(11,N+1)),'sample':{n:[a[n],distinct[n]] for n in [10,11,20,34,35,100,N]}},indent=2))
(L/'outputs'/f'partition-coefficients-{N}.json').write_text(json.dumps({'difference':a,'distinct':distinct}))
