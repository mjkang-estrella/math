# Independent check of Theorems A, B, B', Zsigmondy remark, D counts, F arithmetic.
import math, itertools, time
from math import prod

def Pi(n): return prod(int(c) for c in str(n))
def P(n):
    k=0
    while n>=10: n=Pi(n); k+=1
    return k
def smooth(lim):
    out=[]
    p2=1
    while p2<=lim:
        p3=p2
        while p3<=lim:
            p5=p3
            while p5<=lim:
                p7=p5
                while p7<=lim:
                    out.append(p7); p7*=7
                p5*=5
            p3*=3
        p2*=2
    return sorted(out)

# --- Theorem B: tau table
T10=4996238671872
S=smooth(T10)
tau={}
for m in S:
    p=P(m)
    for k in range(1,p+1):
        if k not in tau: tau[k]=m
print("count 7-smooth <= tau10:",len(S))
print("tau:",[tau[k] for k in sorted(tau)])
claimed=[10,25,49,378,2688,27648,338688,4478976,438939648,4996238671872]
print("tau table matches:", [tau[k] for k in range(1,11)]==claimed, "max P <= tau10:", max(P(m) for m in S))
print("P=10 attained only at tau10:", [m for m in S if P(m)>=10])
print("Pi(tau_k)==tau_{k-1}:", {k: Pi(tau[k])==tau[k-1] for k in range(2,11)})
print("Pi(277777788888899)=",Pi(277777788888899))

# --- Corollary B': max digit product over 7-smooth with D digits, D<=17
S17=smooth(10**17)
best={}
for m in S17:
    D=len(str(m)); v=Pi(m)
    if v>best.get(D,(0,0))[0]: best[D]=(v,m)
for D in range(10,18): print(f"D={D} maxPi={best[D][0]:.3e} at {best[D][1]}  >=tau10? {best[D][0]>=T10}")

# level table: dc(m_i) >= max(dc(tau_{11-i}), first D with maxPi(D) >= tau_{10-i})
S30=smooth(10**30)
mx={}
for m in S30:
    D=len(str(m)); mx[D]=max(mx.get(D,0),Pi(m))
def firstD(t): return min(D for D in mx if mx[D]>=t)
row=[]
for i in range(11):
    lo1 = len(str(tau[11-i])) if 11-i<=10 else 0
    lo2 = firstD(tau[10-i]) if 10-i>=1 else 2
    row.append(max(lo1,lo2))
print("level dc lower bounds:", row, "(claimed 17,13,9,7,6,5,4,3,2,2,2)")
print("persistence>=11 among 7-smooth < 1e30:", [m for m in S30 if P(m)>=11])
print("P=10 among 7-smooth < 1e30:", [m for m in S30 if P(m)==10])

# AM-GM numbers
print("17*tau10^(1/17)=",17*T10**(1/17), " 13*tau9^(1/13)=",13*tau[9]**(1/13))

# --- Zsigmondy remark
print("10^D-1 7-smooth for D<=60:", [D for D in range(1,61) if all(True for _ in [0]) and (lambda x: (lambda f: f(f,x))(lambda f,x: x==1 or any(x%p==0 and f(f,x//p) for p in (2,3,5,7))))(10**D-1)])

# --- Theorem D: factorization counts
def facts(a,b,c,d):
    # multisets over digits 2..9 with product 2^a3^b5^c7^d
    cnt=0; mins=None
    for c8 in range(a//3+1):
      for c4 in range((a-3*c8)//2+1):
        for c9 in range(b//2+1):
          for c6 in range(min(a-3*c8-2*c4, b-2*c9)+1):
            c2=a-3*c8-2*c4-c6; c3=b-2*c9-c6
            if c2<0 or c3<0: continue
            cnt+=1
            L=c2+c3+c4+c6+c8+c9+c+d
            mins=L if mins is None else min(mins,L)
    return cnt,mins
print("factorizations 2^19 3^4 7^6:",facts(19,4,0,6), " 2^4 3^20 7^5:",facts(4,20,0,5))
print("937638166841712 == 2^4 3^20 7^5:", 937638166841712==2**4*3**20*7**5, "P=",P(937638166841712), " tau10==2^19 3^4 7^6:",T10==2**19*3**4*7**6)

# --- Theorem F arithmetic
g=math.log10(9)
print("gamma=",g," gamma^10=",g**10," (1-g^10)/(1-g)=",(1-g**10)/(1-g))
print("max D with floor(g*D)+1<=525:", max(D for D in range(500,700) if math.floor(g*D)+1<=525), " floor(g*549)+1=",math.floor(g*549)+1)
# exact: dc(9^D)
print("exact max D with dc(9^D)<=525:", max(D for D in range(500,700) if len(str(9**D))<=525))
def it(D):
    for _ in range(10): D=len(str(9**D))
    return D
print("max D0 with 10-fold iterate <=525:", max(D for D in range(500,1200) if it(D)<=525))
# Fonga {4,4,7}+j ones member count j<=40
print("members {4,4,7}+j ones, j<=40:", sum((j+3)*(j+2)*(j+1)//2 for j in range(41)))
f=math.factorial
print("record family arrangements j=0:", f(15)//(f(6)*f(6)*f(2)), " j=6:", f(21)//(f(6)**3*f(2)))
