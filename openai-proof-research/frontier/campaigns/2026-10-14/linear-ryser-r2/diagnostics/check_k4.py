#!/usr/bin/env python3
# Myeongjin Kang; no affiliation. Original code MIT.
# Read-only F_4 normal-form check; no search and no external input.
import itertools, json

def mul(a,b):
    ans=0
    for _ in range(2):
        if b&1: ans ^= a
        b >>= 1
        a <<= 1
        if a&4: a ^= 7
    return ans

def slope(p,q):
    x=p[0]^q[0]; y=p[1]^q[1]
    assert x or y
    if not x: return "inf"
    inv=next(z for z in range(1,4) if mul(x,z)==1)
    return mul(y,inv)

P={(0,1):(0,0),(0,2):(3,0),(0,3):(1,2),
   (1,2):(3,3),(1,3):(0,2),(2,3):(1,3)}
dirs={0:"inf",1:0,2:1,3:2}
assert len(set(P.values()))==6
pairs=[]
for e,f in itertools.combinations(P,2):
    d=slope(P[e],P[f]); shared=set(e)&set(f)
    if shared:
        assert d in {dirs[v] for v in set(e)|set(f)}
    else:
        assert d==3 and d not in {dirs[v] for v in set(e)|set(f)}
    pairs.append({"e":list(e),"f":list(f),"join":d,
                  "fresh_agreements":len(shared),"old_agreements":int(not shared)})
singletons=[]
for v,d in dirs.items():
    def intercept(point):
        return point[0] if d=="inf" else point[1]^mul(d,point[0])
    omitted={intercept(P[e]) for e in P if v in e}
    assert len(omitted)==3
    for level in sorted(omitted):
        users=[list(e) for e in P if v not in e and intercept(P[e])==level]
        assert len(users)==1
        singletons.append({"part":v,"old_line_intercept":level,"users":users})
print(json.dumps({"status":"NORMAL_FORM_INCIDENCES_ONLY_NOT_LR", "field_polynomial":"t^2+t+1", "points":6, "pairs":pairs,"old_singletons":singletons},indent=2))
