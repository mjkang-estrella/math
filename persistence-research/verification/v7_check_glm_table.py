# Independent check of GLM Table 1: 7-smooth n (primes 2,3,5,7) whose digits are
# all 1s except at most one digit delta, n < 10^DMAX. Brute force over the lattice.
import sys
DMAX=int(sys.argv[1]); LIM=10**DMAX
found={}
x2=1
while x2<LIM:
    x3=x2
    while x3<LIM:
        x5=x3
        while x5<LIM:
            x7=x5
            while x7<LIM:
                s=str(x7)
                rest=s.replace('1','')
                if len(rest)<=1:
                    d=int(rest) if rest else 1
                    found.setdefault(d,[]).append(x7)
                x7*=7
            x5*=5
        x3*=3
    x2*=2
for d in sorted(found): print(d, sorted(found[d]))
