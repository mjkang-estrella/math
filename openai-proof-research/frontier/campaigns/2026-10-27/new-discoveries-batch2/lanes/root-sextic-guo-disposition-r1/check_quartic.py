import json
def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return c
def der(a): return [i*a[i] for i in range(1,len(a))]
W=[2,0,-2,0,1]
a=mul(W,der(der(W)))
b=mul(der(W),der(W))
K=[-50,0,126,0,-27,0,1]
assert [50*x-37*y for x,y in zip(a,b)]==[8*x for x in K]
def ev(x): return sum(c*x**i for i,c in enumerate(K))
assert [ev(x) for x in [0,1,3,6]]==[-50,50,-374,16150]
intervals=[(-6,-3),(-3,-1),(-1,0),(0,1),(1,3),(3,6)]
assert all(ev(a)*ev(b)<0 for a,b in intervals)
print(json.dumps({'identity':'PASS','six_disjoint_sign_intervals':'PASS','scope':'Exact arithmetic only; positivity follows from W=(x^2-1)^2+1, derivative roots -1,0,1; IVT gives six distinct roots.'}))
