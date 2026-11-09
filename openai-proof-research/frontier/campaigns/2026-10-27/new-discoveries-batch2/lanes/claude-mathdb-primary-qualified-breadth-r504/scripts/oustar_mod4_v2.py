# Bounded exploratory computation (not a proof): ou*(n) mod 4 from OU*(q)=sum_{k>=0} q^{2k+1}(-q;q^2)_k^2.
import sys,json
N=int(sys.argv[1]); M=4
tot=[0]*(N+1)
P=[1]+[0]*N   # (-q;q^2)_{2k}, start k=0 -> 1
k=0
while 2*k+1<=N:
    s=2*k+1
    for i in range(0,N+1-s): tot[i+s]=(tot[i+s]+P[i])%M
    # multiply P by (1+q^{2k+1})^2 so P=(-q;q^2)_{k+1}^2
    for e in (2*k+1,2*k+1):
        for i in range(N,e-1,-1): P[i]=(P[i]+P[i-e])%M
    k+=1
res={}
for m in (50,98,242,100,196,484):
    res[m]={'odd_r':[r for r in range(m) if r%2==1 and all(tot[n]==0 for n in range(max(r,1),N+1,m))],
            'even_r':[r for r in range(m) if r%2==0 and all(tot[n]==0 for n in range(max(r,2),N+1,m))]}
ev=[n for n in range(2,N+1,2) if tot[n]==0]
print(json.dumps({'N':N,'first':tot[:30],'zero_mod4_frac_even':len(ev)/(N//2),'zero_mod4_frac_odd':sum(1 for n in range(1,N+1,2) if tot[n]==0)/((N+1)//2),'aps':res}))
