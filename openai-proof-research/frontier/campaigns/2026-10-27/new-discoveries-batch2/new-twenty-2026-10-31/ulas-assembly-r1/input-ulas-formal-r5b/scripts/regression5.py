from math import comb
# Independent defining-product calculation; no Lean or review code imported.
N=400
C=[1]+[0]*N
for step in [1,1,2,4,8,16,32,64,128,256]:
    for n in range(step,N+1): C[n]+=C[n-step]
def mul(a,b):
    return [sum(a[i]*b[n-i] for i in range(n+1)) for n in range(len(a))]
def v2(z):
    assert z>0
    return (z&-z).bit_length()-1
P=[1]+[0]*N
checks=0
for m in range(1,65):
    P=mul(P,C)
    for n in range(1,N//4+1):
        d=P[4*n]-P[n]
        assert d>0
        v=v2(d)-v2(n)
        if m%4==1:
            assert v>=3
            if n%2: assert v==3
        if m%4==3:
            assert v>=6
            if m%16 in (3,7) and n%2: assert v==6
            if m%16==11 and n%4==2: assert v==6
            if m%16==15: assert v>=7
        checks+=1
    if m==15:assert P[4]-P[1]==48000
print('PASS',checks,'positive differences and all applicable odd claims; m=15 difference 48000')
