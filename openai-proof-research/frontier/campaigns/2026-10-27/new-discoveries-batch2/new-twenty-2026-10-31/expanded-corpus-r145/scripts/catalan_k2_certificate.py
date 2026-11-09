# Exact certificate that MathDB 343469 (Gao-Gu Conjecture 4.12) fails as printed (n>=2) for k=2.
# Exact big-integer height DP (independent of the mod-2^64 code) plus brute-force Dyck enumeration for n<=12.
import math,json,itertools
def wcat_exact(b,N):
    dp=[1]; out=[1]
    for step in range(1,2*N+1):
        top=min(step,2*N-step); new=[0]*(top+1)
        for h in range(top+1):
            x=dp[h-1]*b(h-1) if 1<=h<=len(dp) else 0
            if h+1<len(dp): x+=dp[h+1]
            new[h]=x
        dp=new
        if step%2==0: out.append(dp[0])
    return out
def brute(n,b):
    tot=0
    for ups in itertools.combinations(range(2*n),n):
        S=set(ups); h=0; w=1; ok=True
        for i in range(2*n):
            if i in S: w*=b(h); h+=1
            else:
                h-=1
                if h<0: ok=False;break
        if ok: tot+=w
    return tot
v2=lambda x:(x&-x).bit_length()-1
s2=lambda n:bin(n).count('1')
k=2; b=lambda h:(2*h+1)**(2*k)
L=wcat_exact(b,19); C=[math.comb(2*n,n)//(n+1) for n in range(20)]
for n in range(0,13): assert brute(n,b)==L[n]
rows={n:dict(L=str(L[n]),C=C[n],diff_v2=v2(L[n]-C[n]),s2=s2(n),e=v2(L[n]-C[n])-s2(n)) for n in (2,3,4,5,19)}
assert rows[3]['L']=='57349' and L[3]-C[3]==7*2**13
e={n:rows[n]['e'] for n in rows}
assert (e[2],e[3],e[4],e[5],e[19])==(3,11,3,4,8)
proof=["If alpha were even, xi2(3-alpha)=xi2(5-alpha)=0, so e(3)=e(5)=c; but e(3)=11 != 4=e(5). Hence alpha is odd.",
"alpha odd gives xi2(2-alpha)=0, hence c=e(2)=3.",
"Then xi2(3-alpha)=e(3)-c=8, so alpha = 3 mod 256, hence 19-alpha = 16 mod 256 and xi2(19-alpha)=4.",
"But e(19)-c=5: contradiction. So no 2-adic integer alpha_2 and integer c_2 satisfy the identity for all n>=2.",
"Note n>=4 is consistent with a 2-adic fit for k=2 through n<=1100 (logs/catalan-scan-1100-a.log): the failure is the single endpoint value n=3."]
out=dict(k=k,rows=rows,proof=proof,brute_force_agreement_n_le=12)
print(json.dumps(out,indent=1))
open('outputs/catalan-k2-certificate.json','w').write(json.dumps(out,indent=1)+'\n')
