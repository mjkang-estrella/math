#!/usr/bin/env python3
"""Exact exploratory forward differences of rank-two symmetric-power Chern classes.

Source2605.25271v1 Conjectures3.2/3.3. This is not a formal source bridge.
For each d, expand product(i=0..d)(1+i*x+(d-i)*y) exactly over integers;
Schur coefficients are adjacent monomial differences. Forward differences
at d=0 give coefficients of binomial(d,r), up to the degree bound2k.
"""
import argparse
import json
from pathlib import Path


def values(d, n):
    rows = [[0] * (k + 1) for k in range(n + 1)]
    rows[0][0] = 1
    for i in range(d + 1):
        for k in range(min(n, i + 1), 0, -1):
            for j in range(k + 1):
                rows[k][j] += (i * rows[k-1][j] if j < k else 0) + (
                    (d-i) * rows[k-1][j-1] if j else 0)
    return {(k,j): rows[k][j] - (rows[k][j-1] if j else 0)
            for k in range(n + 1) for j in range(k//2 + 1)}


def forward(seq):
    out = []
    while seq:
        out.append(seq[0])
        seq = [b-a for a,b in zip(seq,seq[1:])]
    return out


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--degree',type=int,default=30)
    args=ap.parse_args();n=args.degree
    allvalues=[values(d,n) for d in range(2*n+3)]
    checks=0; failures=[]; negative=[]
    for k in range(n+1):
        for j in range(k//2+1):
            b=forward([v[k,j] for v in allvalues])
            assert all(x==0 for x in b[2*k+1:]),(k,j,'degree check')
            b=b[:2*k+1]
            for r,x in enumerate(b):
                if x<0:negative.append(dict(k=k,j=j,r=r,value=x))
            for r in range(1,len(b)-1):
                checks+=1
                if b[r]*b[r] < b[r-1]*b[r+1]:
                    failures.append(dict(k=k,j=j,r=r,triple=b[r-1:r+2]))
        print('degree',k,'checked; violations',len(failures),'negative',len(negative),flush=True)
    result=dict(status='exact finite exploration only, credit0',degree=n,
                checks=checks,negative=negative,logconcavity_failures=failures)
    Path(__file__).with_name('mode-check.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
