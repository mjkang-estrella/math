"""MathDB 371202: P(n) distribution of Fibonacci minima, claimed arctan formula.
Decisive check: empirical density over uniform integer box vs claimed formula.
a_n for standard recurrence: a_n = F_{n-1} a_0 + F_n a_1 (n>=1, F_{-1}=1,F_0=0... use a_1=a_1).
We use a_n = a_{n-1}+a_{n-2}, n>=2, a_0,a_1 given. |a_n| grows ~ phi^n; argmin over n>=0.
Chiral: a_n = -a_{n-1}+a_{n-2}. The claim P(n) is probability minimum at position n; which recurrence? 'and its chiral recurrence' — presumably P(n) for the pair combined? The formula: P(0)=1/4 suggests symmetry between the two recurrences (each contributing 1/2, and P(0)=1/4 each?). We test the standard recurrence alone first: empirical P_std(n) should be 2*P(n)? We compare shapes: P_std(n) vs formula*2 for n>=1 and P_std(0)=1/2."""
import math, random
random.seed(20261030)
F=[0,1]
while F[-1] < 10**18: F.append(F[-1]+F[-2])
def argmin_pos(a0,a1,mode):
    # iterate until |a_n| clearly increasing beyond min; sequence |a_n| grows like phi^n after min region
    a,b=a0,a1; best=abs(a); bi=0; n=0
    hist=[abs(a)]
    if mode=='std':
        while True:
            n+=1; a,b=b,a+b; v=abs(b); hist.append(v)
            if v<best: best=v; bi=n
            if n>12 and v>best*2 and v>10**6 and v>hist[n-1]: # safely past min
                if v > 4*best and v>2*hist[n-2]: break
    else:
        while True:
            n+=1; a,b=b,b-a; v=abs(b); hist.append(v)
            if v<best: best=v; bi=n
            if n>12 and v>4*best and v>10**6: break
    return bi
N=400000
cnt={}
for _ in range(N):
    a0=random.randint(-3000,3000); a1=random.randint(-3000,3000)
    bi=argmin_pos(a0,a1,'std')
    cnt[bi]=cnt.get(bi,0)+1
def P_formula(n):
    L=[2,1]
    while len(L)<n+3: L.append(L[-1]+L[-2])
    if n==0: return 1/4
    if n==1: return None
    if n%2==0:
        return (math.atan(L[n-2]/L[n-1])-math.atan(L[n]/L[n+1]))/math.pi
    else:
        return (math.atan(L[n]/L[n+1])-math.atan(L[n-2]/L[n-1]))/math.pi
print("empirical std-recurrence P(n) (x2 for n>=1) vs 2*formula:")
for n in range(0,12):
    emp=cnt.get(n,0)/N
    f=P_formula(n)
    print(n, f"emp={emp:.6f}", (f"2*formula={2*f:.6f} diff={emp-2*f:+.2e}" if f else "n=1: formula undefined?"))
# sum check
s=sum(cnt.get(n,0) for n in range(0,30))/N
print("mass n<=29:", s)
