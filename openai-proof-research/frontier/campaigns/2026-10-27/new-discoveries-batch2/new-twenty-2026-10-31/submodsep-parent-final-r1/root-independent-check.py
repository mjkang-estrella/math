import itertools
coords=[(i,) for i in range(5)]+list(itertools.combinations(range(5),2))
def q(X):
    m=0
    for k,S in enumerate(coords):
        if set(S)<=X: m|=1<<k
    return m
good={q(set(X)) for r in range(6) for X in itertools.combinations(range(5),r)}
assert len(good)==32
rows=[(103,5743,5646),(5743,1067,19899),(1067,5359,4301),(5359,103,11127)]
FULL=(1<<15)-1
ok=True
for a,b,c in rows:
    c&=FULL  # masks above 2^15 would be outside the face; check
    meet=a&c; join=a|c
    other = meet if join==b else (join if meet==b else None)
    print(a,b,c,'c good',c in good,'meet',meet,'join',join,'b is',('join' if join==b else 'meet' if meet==b else 'NEITHER'),'other bad',other is not None and other not in good)
    ok &= (c in good) and other is not None and (other not in good)
print('cycle closes', rows[-1][1]==rows[0][0], 'all rows valid', ok)
