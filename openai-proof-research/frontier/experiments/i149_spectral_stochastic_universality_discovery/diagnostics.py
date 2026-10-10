"""New finite checks only. No source/ancestor diagnostic execution."""
from fractions import Fraction as F
from itertools import product

def run():
    counts = {'jump_operator_adjoint': 0, 'two_jump_integrand': 0,
              'L2_contraction': 0, 'single_site_history_derivative': 0}
    for n, colors in [(1,2),(2,2),(2,4),(3,2)]:
        states = list(product((0,1), repeat=n))
        ids = {x:i for i,x in enumerate(states)}
        flip = [[ids[x[:j]+(1-x[j],)+x[j+1:]] for j in range(n)] for x in states]
        transitions = []
        for a in [F(0),F(1,4),F(1,2),F(3,4),F(1)]:
            p=(1-a)/2
            transitions.append([[p**sum(u!=v for u,v in zip(x,y)) *
                                (1-p)**sum(u==v for u,v in zip(x,y))
                                for y in states] for x in states])
        for values in product(range(colors),repeat=len(states)):
            I=[[int(values[j]!=values[i]) for j in row] for i,row in enumerate(flip)]
            N=list(map(sum,I))
            adj=[0]*len(states)
            for i,row in enumerate(flip):
                for v,j in enumerate(row):
                    assert I[i][v]==I[j][v]
                    adj[j]+=I[i][v]
            assert adj==N
            counts['jump_operator_adjoint']+=1
            second=F(sum(t*t for t in N),len(states))
            for P in transitions:
                PN=[sum(p*t for p,t in zip(row,N)) for row in P]
                left=F(sum(sum(I[i][v]*PN[j] for v,j in enumerate(row))
                           for i,row in enumerate(flip)),len(states))
                right=F(sum(x*y for x,y in zip(N,PN)),len(states))
                assert left==right
                assert right<=second
                counts['two_jump_integrand']+=1
                counts['L2_contraction']+=1
    for gaps in product([F(1,3),F(1),F(2)],repeat=3):
        for h in product((0,1),repeat=4):
            derivative=F(0)
            for j,dt in enumerate(gaps):
                if all(h[k]==h[k+1] for k in range(3) if k!=j):
                    derivative+=dt*F(1 if h[j]!=h[j+1] else -1,4)
            explicit=F(0)
            for j,dt in enumerate(gaps):
                up=(0,)*(j+1)+(1,)*(3-j)
                down=(1,)*(j+1)+(0,)*(3-j)
                explicit+=dt*F(int(h==up)+int(h==down)-int(h==(0,)*4)-int(h==(1,)*4),4)
            assert derivative==explicit
            counts['single_site_history_derivative']+=1
    return {'status':'PASS','arithmetic':'integers and fractions.Fraction',
            'checks':counts,'scope':'finite Boolean-clock identities only; not percolation estimates, universal mathematics, novelty or acceptance'}

if __name__=='__main__':
    import json
    print(json.dumps(run(),sort_keys=True,indent=2))
