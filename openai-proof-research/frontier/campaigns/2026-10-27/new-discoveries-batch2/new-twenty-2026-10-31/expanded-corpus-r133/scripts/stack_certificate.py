# Exact integer certificate checks for lim d_n^{1/n} >= 1.73, using P_n = n! d_n from stack_pairs_int.py output.
import json, math, sys
P={int(k):int(v) for k,v in json.load(open(sys.argv[1])).items()}
for a in sorted(P):
    # doubling bound: lim >= (d_a/(4(a+1)))^{1/(a+1)} > 1.73  <=>  P_a*100^(a+1) > 4(a+1) a! 173^(a+1)
    dbl = P[a]*100**(a+1) > 4*(a+1)*math.factorial(a)*173**(a+1)
    # source Thm 2.5 bound with n=a+1>=8: lim >= (d_a/n^2)^{1/n}
    n=a+1; src = n>=8 and P[a]*100**n > n*n*math.factorial(a)*173**n
    if dbl or src or a%10==0: print(a, 'doubling>1.73:',dbl, 'source-sup>1.73:',src, 'float doubling', (P[a]/math.factorial(a)/(4*(a+1)))**(1/(a+1)))
