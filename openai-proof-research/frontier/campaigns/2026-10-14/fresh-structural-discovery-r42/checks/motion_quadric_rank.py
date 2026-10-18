#!/usr/bin/env python3
"""MIT. Finite-field restriction-rank diagnostic; not a theorem over all real clouds."""
import itertools,json,math,random
PRIME=1000003
SEED=16642

def exponents(n,d):
    if n==1:
        yield (d,);return
    for a in range(d+1):
        for b in exponents(n-1,d-a):yield (a,)+b

def mul(a,b):
    out={}
    for u,x in a.items():
        for v,y in b.items():
            z=tuple(i+j for i,j in zip(u,v));out[z]=(out.get(z,0)+x*y)%PRIME
    return {u:x for u,x in out.items() if x}

def restriction(p,d,mons):
    x,y,z=p
    # c=-w cross p: (-z*w2+y*w3,z*w1-x*w3,-y*w1+x*w2).
    lin=[{(1,0,0):1},{(0,1,0):1},{(0,0,1):1},
         {(0,1,0):-z,(0,0,1):y},{(1,0,0):z,(0,0,1):-x},
         {(1,0,0):-y,(0,1,0):x}]
    powers=[]
    for a in lin:
        q=[{(0,0,0):1}]
        for i in range(d):q.append(mul(q[-1],a))
        powers.append(q)
    outmons=[a for k in range(d+1) for a in exponents(3,k)]
    rows={a:[0]*len(mons) for a in outmons}
    for j,m in enumerate(mons):
        f={(0,0,0):1}
        for i,k in enumerate(m):f=mul(f,powers[i][k])
        for a,v in f.items():rows[a][j]=v%PRIME
    return list(rows.values())

def append_rows(basis,rows):
    for v in rows:
        for j in range(len(v)):
            if not v[j]:continue
            if j in basis:
                a=v[j];u=basis[j]
                for k in range(j,len(v)):v[k]=(v[k]-a*u[k])%PRIME
            else:
                a=pow(v[j],PRIME-2,PRIME)
                basis[j]=[(x*a)%PRIME for x in v];break

def main():
    assert all(PRIME%j for j in range(2,math.isqrt(PRIME)+1)), 'modulus must be prime'
    rng=random.Random(SEED);pts=[]
    while len(pts)<40:
        p=tuple(rng.randrange(-100,101) for _ in range(3))
        if p not in pts:pts.append(p)
    ans=[]
    for d in range(1,5):
        mons=[a for k in range(d+1) for a in exponents(6,k)]
        h=math.comb(d+6,6)-(math.comb(d+4,6) if d>=2 else 0)
        b={};track=[]
        for i,p in enumerate(pts,1):
            append_rows(b,restriction(p,d,mons));track.append({'pins':i,'rank':len(b)})
            assert len(b)<=h
            if len(b)==h:break
        assert len(b)==h,'this finite sample did not saturate the quadric rank'
        ans.append({'degree':d,'ambient_polynomials':len(mons),'quadric_rank':h,'first_full_rank_pin_count':len(track),'track':track})
    return {'prime':PRIME,'seed':SEED,'points':pts,'results':ans,'interpretation':'Each displayed modular rank is a rigorous lower bound on the same integer restriction matrix over Q. Saturation shows its kernel consists exactly of multiples of w dot c through degree D, for these finite rational clouds only. This does not prove a generic asymptotic, the pinned target, or impossibility of different polynomial constructions.'}
if __name__=='__main__':print(json.dumps(main(),indent=2))
