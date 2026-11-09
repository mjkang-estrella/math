import json

def coefficients(m,N):
    a=[1]+[0]*N
    for _ in range(m):
        for step in [1]+[2**i for i in range(N.bit_length())]:
            for j in range(step,N+1): a[j]+=a[j-step]
    return a

def v2(x):
    assert x
    return (abs(x)&-abs(x)).bit_length()-1
rows=[]
for m in range(1,17):
    a=coefficients(m,128)
    for n in range(1,33):
        d=a[4*n]-a[n]
        target=v2(n)+(2*v2(m//2)+3 if m%2==0 else 3 if m%4==1 else 6)
        assert d>0 and v2(d)>=target
        if m%2==0: assert v2(d)==target
        if m%16==15: assert v2(d)>target
        if m%16 in (3,7) and n%2==0 and v2(d)==target: rows.append([m,n,d,v2(d)])
a=coefficients(15,4)
assert a[4]-a[1]==48000
print(json.dumps(dict(c15=a, difference=48000, extra_even_equalities=rows, checked_pairs=512),indent=2))
