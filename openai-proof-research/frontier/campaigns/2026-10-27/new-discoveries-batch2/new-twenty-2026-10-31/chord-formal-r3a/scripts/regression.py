import itertools,json,pathlib

def matchings(points):
    if not points:
        yield {}; return
    p=points[0]
    for q in points[1:]:
        for d in matchings([x for x in points if x not in (p,q)]):
            yield d|{p:q,q:p}

def face(t,c):
    L=len(t)
    out=[]
    for h in range(3*L):
        i,r=divmod(h,3)
        if r==0: j,s=(i-1)%L,1
        elif r==1: j,s=(i+1)%L,0
        else: j,s=t[i],2
        out.append(3*j+((2,0,1) if c[j] else (1,2,0))[s])
    return out

def count(f):
    seen=set(); k=0
    for i in range(len(f)):
        if i in seen: continue
        k+=1; j=i
        while j not in seen: seen.add(j); j=f[j]
    return k

def boundary(t,c): return count(face(t,c)) if t else 2
rows=[]
for n in range(1,6):
    cases=0
    for t in matchings(list(range(2*n))):
        for bits in itertools.product((False,True),repeat=2*n):
            f=face(t,bits); b=count(f)
            for p in range(2*n):
                q=t[p]
                if p>q: continue
                keep=[i for i in range(2*n) if i not in (p,q)]
                idx={x:i for i,x in enumerate(keep)}
                small={idx[i]:idx[t[i]] for i in keep}
                bs=boundary(small,[bits[i] for i in keep])
                swapped=f.copy()
                swapped[3*p+2],swapped[3*q+2]=swapped[3*q+2],swapped[3*p+2]
                assert count(swapped)==bs, (n,t,bits,p,'erasure')
                assert abs(bs-b)==1, (n,t,bits,p,'deletion')
                cases+=1
    rows.append({'n':n,'deletions_and_band_erasures':cases})
    print(json.dumps(rows[-1]),flush=True)
controls={'wrong_empty_annulus':boundary({},[])!=0,
          'wrong_euler_offset':boundary({0:3,1:4,2:5,3:0,4:1,5:2},[False]*6)+2!=4,
          'wrong_surgery_identity':any(boundary({0:1,1:0},bits)!=2 for bits in itertools.product((False,True),repeat=2))}
assert all(controls.values())
pathlib.Path('regression.json').write_text(json.dumps({'rows':rows,'negative_controls':controls},indent=2)+'\n')
