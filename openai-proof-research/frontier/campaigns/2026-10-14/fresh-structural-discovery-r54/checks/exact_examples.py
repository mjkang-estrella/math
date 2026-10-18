#!/usr/bin/env python3
"""MIT. Exact finite diagnostics, not a proof or a multicommodity solver."""
from itertools import combinations
from fractions import Fraction
import json

def check(n,edges,g,sets):
    count=0; maximum=Fraction(0)
    for selected in sets:
        A=set(selected)
        if not A:continue
        D=[[10**6]*n for _ in range(n)]
        for i in range(n):D[i][i]=0
        for j,(u,v) in enumerate(edges):D[u][v]=D[v][u]=g-1 if j in A else 1
        for k in range(n):
            for i in range(n):
                for j in range(n):D[i][j]=min(D[i][j],D[i][k]+D[k][j])
        assert all(D[u][v]==(g-1 if j in A else 1) for j,(u,v) in enumerate(edges))
        top=sum(D[u][v] for j,(u,v) in enumerate(edges) if j in A)
        bottom=sum(D[u][v] for u,v in edges)
        r=Fraction(top,bottom)
        assert r==Fraction(len(A)*(g-1),len(edges)+len(A)*(g-2))
        maximum=max(maximum,r);count+=1
    return {'n':n,'m':len(edges),'girth_lower_bound':g,'nonempty_subsets_checked':count,'largest_dual_quotient':str(maximum)}

def main():
    rows=[]
    for n in range(3,10):
        E=[(i,(i+1)%n) for i in range(n)]
        rows.append({'family':'cycle','protocol':'all nonempty edge subsets',**check(n,E,n,(A for s in range(1,n+1) for A in combinations(range(n),s)))})
    E=[(i,(i+1)%5) for i in range(5)]+[(i,i+5) for i in range(5)]+[(i+5,(i+2)%5+5) for i in range(5)]
    rows.append({'family':'Petersen','protocol':'all7-edge subsets (not all trees or all subsets)',**check(10,E,5,combinations(range(15),7))})
    E=[(i,j) for i in range(2) for j in range(2,5)]
    rows.append({'family':'K2,3','protocol':'all nonempty edge subsets',**check(5,E,4,(A for s in range(1,7) for A in combinations(range(6),s)))})
    x=[3,3,-2,-2,-2];D=[[0 if i==j else 2 if (i<2)==(j<2) else 1 for j in range(5)] for i in range(5)]
    q=sum(x[i]*D[i][j]*x[j] for i in range(5) for j in range(5));assert sum(x)==0 and q==12
    return {'status':'PASS','metric_examples':rows,'total_subsets':sum(r['nonempty_subsets_checked'] for r in rows),'PSD_obstruction':{'sum_x':0,'xTDx':q,'xTZx':-q//2},'scope':'Finite arithmetic only. Universal girth proof is in working.md. No LP optimization, theorem of novel upper bound, or independent gate.'}
if __name__=='__main__':print(json.dumps(main(),indent=2))
