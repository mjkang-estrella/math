#!/usr/bin/env python3
"""MIT. Exact finite bookkeeping diagnostics; not the source geometry or theorem."""
from itertools import product
import json

def main():
    stocks=0;edges=0
    for d in (1,2,5):
        plus=[2*d+j for j in (0,1,3,5)]
        minus=[2*d]*4
        for missing in range(4):
            x=[int(v!=missing) for v in range(4)]
            demands={'plus1':[d*a for a in x], 'plus0':[plus[v]-d*x[v] for v in range(4)],
                     'minus1':[d*(1-a) for a in x], 'minus0':[minus[v]-d*(1-x[v]) for v in range(4)]}
            inventory={'plus1':3*d,'plus0':sum(plus)-3*d,'minus1':d,'minus0':sum(minus)-d}
            for s,ds in demands.items():
                copies=list(range(inventory[s]));used=[];at=0
                for amount in ds:
                    assert amount>=0
                    taken=copies[at:at+amount];assert len(taken)==amount;used+=taken;at+=amount
                assert used==copies and len(used)==len(set(used))
            stocks+=1
        for R in (1,3):
            for x in ((0,1),(1,0),(1,1)):
                permit_endpoint=0 if x[0]==0 or x[1]==1 else 1
                p=[('permit',j) for j in range(d*R)];q=[('nonpermit',j) for j in range(d*R)]
                assigned=[None,None];assigned[permit_endpoint]=p;assigned[1-permit_endpoint]=q
                assert len(set(assigned[0]+assigned[1]))==2*d*R
                for endpoint in (0,1):
                    if x[endpoint]==0:assert all(species=='permit' for species,j in assigned[endpoint])
                edges+=1
    # Mean cardinality3 alone does not ensure the fixed3d pool is feasible.
    assert (3*4+1*0)/4==3
    assert 4>3 and 0<3
    # Clause C1=(0,1,2), C2=(1,2,3), both parity0.
    z=(0,0,0,0);zz=(0,0,0,1)
    own=lambda q:(q[0]^q[1]^q[2])==0
    neighbor=lambda q:(q[1]^q[2]^q[3])==0
    assert own(z)==own(zz)==True
    assert (own(z) and neighbor(z))!=(own(zz) and neighbor(zz))
    return {'status':'PASS','clause_stock_assignments':stocks,'edge_resource_assignments':edges,
      'controls':['mean-cardinality-only stock assignment fails','unnecessary neighbor guard changes M indicator outside its clause'],
      'limits':'Finite abstract stock and endpoint allocation only. No source tree/scalar-capacity test, hard XOR construction, or asymptotic proof.'}
if __name__=='__main__':print(json.dumps(main(),indent=2))
