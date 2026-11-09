# Hoffman ratio bound for Cay(F_p^3, S), S=±{(a^2,2ab,b^2)}: eigenvalues sum_{s in S} cos(2 pi <w,s>/p).
import sys,itertools,cmath,math
p=int(sys.argv[1])
S=set()
for a in range(p):
    for b in range(p):
        if a or b:
            s=((a*a)%p,(2*a*b)%p,(b*b)%p); S.add(s); S.add(tuple((-c)%p for c in s))
d=len(S); lmin=1e9
for w in itertools.product(range(p),repeat=3):
    if not any(w): continue
    lam=sum(math.cos(2*math.pi*(sum(x*y for x,y in zip(w,s))%p)/p) for s in S)
    lmin=min(lmin,lam)
N=p**3
print('p',p,'deg',d,'lambda_min',round(lmin,6),'Hoffman bound slice',round(N*(-lmin)/(d-lmin),4),'q^2',p*p)
