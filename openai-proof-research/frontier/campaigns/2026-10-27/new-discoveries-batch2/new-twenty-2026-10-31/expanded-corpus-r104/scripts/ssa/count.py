# Independent count of |C_n(S)| by brute force (small n) and DP over last-4 letters (any n); compares S vs TC.
import itertools,sys,math
D=sys.argv[1]; al='ACGT'
S=set(open(D+'/outputs/ssa5-best-set.txt').read().split())
TC={''.join(t) for t in itertools.product(al,repeat=5) if sum(c in 'TC' for c in t)>=3}
def brute(X,n): return sum(all(''.join(x[i:i+5]) in X for i in range(n-4)) for x in itertools.product(al,repeat=n))
def dp(X,n):
    cnt={''.join(t):1 for t in itertools.product(al,repeat=4)}
    for _ in range(n-4):
        new={}
        for s,c0 in cnt.items():
            for c in al:
                if s+c in X: new[(s+c)[1:]]=new.get((s+c)[1:],0)+c0
        cnt=new
    return sum(cnt.values())
for n in range(5,9): assert brute(S,n)==dp(S,n) and brute(TC,n)==dp(TC,n)
print('brute==dp for n=5..8')
first=None
for n in range(5,801):
    a,b=dp(S,n),dp(TC,n)
    if a>b and first is None: first=n
    if n in (5,10,20,50,100,200,500,800): print(n,a>b,math.log2(a)/n,math.log2(b)/n)
print('first n with |C_n(S)|>|C_n(TC)|:',first)
