"""Run ONLY through the assigned helper_guard.py, with prescribed thread env.
Exact finite controls; these are not a proof of the prime-power lemma.
"""
from math import comb, gcd, lcm
from fractions import Fraction as F
from pathlib import Path
import json

def coefficients(k, r):
    return [(-1)**i * comb(k,i)*comb(k+r+i-1,i) for i in range(k+1)]

def run():
    matrix_cases=0
    for r in range(1,17):
        for n in range(1,10):
            c=[coefficients(k,r) for k in range(n)]
            B=[[sum(F(2*k+r,r)*c[k][i]*c[k][j]
                    for k in range(max(i,j),n)) for j in range(n)] for i in range(n)]
            R=[[F(1,comb(i+j+r,r)) for j in range(n)] for i in range(n)]
            assert all(sum(B[i][k]*R[k][j] for k in range(n)) == (i==j)
                       for i in range(n) for j in range(n))
            assert B[0][0]==F(n*(n+r-1),r)
            matrix_cases+=1
    denominator_cases=0
    for r in range(1,97):
        S=[[0]*48 for _ in range(48)]
        for k in range(48):
            c=coefficients(k,r)
            for i in range(k+1):
                for j in range(i,k+1):
                    S[i][j]+=(2*k+r)*c[i]*c[j]
            n=k+1
            den=1
            for i in range(n):
                for j in range(i,n): den=lcm(den,r//gcd(r,S[i][j]))
            assert den==r//gcd(r,n*(n-1)),(n,r,den)
            denominator_cases+=1
    # Stronger block congruence suggested for lifting, independently sampled.
    blocks=0
    for p in [2,3,5,7]:
        for e in range(1,4):
            q=p**e
            if q>50:continue
            for r in [q,2*q,3*q]:
                for t in range(3):
                    C=[coefficients(k,r) for k in range((t+1)*q)]
                    for i in range(min(16,(t+1)*q)):
                        for j in range(i,min(16,(t+1)*q)):
                            z=sum((2*k+r)*C[k][i]*C[k][j]
                                  for k in range(max(t*q,i,j),(t+1)*q))
                            assert z%q==0,(p,e,r,t,i,j,z%q)
                            blocks+=1
    return dict(status='PASS',exact_matrix_cases=matrix_cases,
                denominator_cases=denominator_cases,block_entry_cases=blocks,
                limit='Finite controls only; higher prime-power theorem remains unproved.')

if __name__=='__main__':
    result=run()
    (Path(__file__).parent/'check-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))
