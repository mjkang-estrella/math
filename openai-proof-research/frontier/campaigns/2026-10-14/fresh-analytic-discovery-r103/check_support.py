#!/usr/bin/env python3
"""Original exact finite supporting checks; not a proof of the process theorem."""
from fractions import Fraction as Q
from itertools import product
import json


def run():
    triples=[(w,u,b) for w,u,b in product((0,1),repeat=3) if w<=u<=b]
    counts={'single_jump_birth':0,'single_jump_death':0,'refresh':0,'pair_kernel':0}
    rejected={'omit_drift':False,'omit_half_D_drift':False,'double_refresh_term':False,
              'omit_pair_mixed_indicator':False,'omit_geometry_cross_term':False}
    for w,u,b in triples:
        p=b-w; drift=Q(w+b,2)-u
        for vals in product((0,1),repeat=4):
            f=lambda x,y:Q(vals[2*x+y])
            A=f(0,0);B=f(1,0)-A;C=f(0,1)-A;D=f(1,1)-A-B-C
            birth=sum((f(u,v)-f(u,u) for v in (w,b)),Q(0))/2
            death=sum((f(v,u)-f(u,u) for v in (w,b)),Q(0))/2
            principal=-D*p/4
            assert birth==(C+D/2)*drift+principal
            assert death==(B+D/2)*drift+principal
            refresh=sum((f(v0,v1)-f(v0,v0) for v0,v1 in product((w,b),repeat=2)),Q(0))/4
            assert refresh==principal
            for key in ('single_jump_birth','single_jump_death','refresh'):counts[key]+=1
            rejected['omit_drift']|=birth!=principal
            rejected['omit_half_D_drift']|=birth!=C*drift+principal
            rejected['double_refresh_term']|=birth!=(C+D/2)*drift+2*principal
    for (w,u,b),(ww,uu,bb) in product(triples,repeat=2):
        lhs=Q((w-u)*(ww-uu)+(b-u)*(bb-uu),2)
        rhs=Q((b-w)*(bb-ww),2)*int(u==uu)
        assert lhs==rhs;counts['pair_kernel']+=1
        rejected['omit_pair_mixed_indicator']|=lhs!=Q((b-w)*(bb-ww),2)
    for x,y in product((Q(0),Q(1),Q(2)),repeat=2):
        assert x*y-1==(x-1)+(y-1)+(x-1)*(y-1)
        rejected['omit_geometry_cross_term']|=x*y-1!=(x-1)+(y-1)
    # Exact boundaries of the E/W Voronoi edge in the four-site example.
    south=Q(1,2);north=Q(3)
    lower=(1-south*south)/(2*south);upper=(north*north-1)/(2*north)
    assert lower==Q(3,4) and upper==Q(4,3) and lower<1<upper
    # Along y=1, white-minus-nearest-black squared distances are
    # 2|x|+1/4 (south) and 2|x|+2 (north), strictly positive for all x.
    assert (1+south)**2-2==Q(1,4) and (north-1)**2-2==2
    # On x=0,y<=0, black-minus-south distance is 3/4-y>0.
    assert 1-south*south==Q(3,4)
    assert all(rejected.values())
    return {'status':'PASS_FINITE_SUPPORT_ONLY','counts':counts,'negative_controls':rejected,
            'boundary_edge':[str(lower),str(upper)],'full_theorem_checked':False}

if __name__=='__main__':print(json.dumps(run(),indent=2,sort_keys=True))
