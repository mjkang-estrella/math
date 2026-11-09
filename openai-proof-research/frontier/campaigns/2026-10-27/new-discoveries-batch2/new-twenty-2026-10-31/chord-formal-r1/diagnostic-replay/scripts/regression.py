import json, itertools, pathlib

def matchings(xs):
    if not xs:
        yield (); return
    a,*ys=xs
    for b in ys:
        for rest in matchings([x for x in ys if x!=b]):
            yield ((a,b),)+rest

def pair(n,edges):
    t=[0]*(2*n)
    for a,b in edges:t[a]=b;t[b]=a
    return t

def count(p):
    seen=set(); ans=0
    for i in range(len(p)):
        if i not in seen:
            ans+=1;j=i
            while j not in seen:seen.add(j);j=p[j]
    return ans

def boundary(t,m):
    L=len(t)
    if not L:return 2
    flip=[]
    for h in range(3*L):
        i,k=divmod(h,3)
        j=(i-1)%L if k==0 else (i+1)%L if k==1 else t[i]
        q=1 if k==0 else 0 if k==1 else 2
        rot=(2,0,1) if m>>j&1 else (1,2,0)
        flip.append(3*j+rot[q])
    return count(flip)

def dart(t,m):
    L=len(t);sg=[]
    for i in range(L):
        step=-1 if m>>i&1 else 1
        j=(i+step)%L
        while (m>>j&1)!=(m>>i&1):j=(j+step)%L
        sg.append(j)
    return count([sg[t[i]] for i in range(L)])+(m==0)+(m==(1<<L)-1)

def canon(t):
    L=len(t)
    return min(tuple((t[(s+e*i)%L]-s)*e%L for i in range(L)) for s in range(L) for e in [1,-1])

def gr(t):
    n=len(t)//2;out=set()
    for m in range(1<<len(t)):
        b=boundary(t,m)
        assert b<=n+2 and (n+2-b)%2==0
        out.add((n+2-b)//2)
        assert b==dart(t,m)
    return sorted(out)

rows=[]
for n in range(1,6):
    classes={};pairs=0
    for edges in matchings(list(range(2*n))):
        t=pair(n,edges);g=gr(t);pairs+=1<<len(t)
        classes[canon(t)]=g
    row={'n':n,'labelled_matchings':len(list(matchings(list(range(2*n))))),
         'classes':len(classes),'assignments_checked':pairs,
         'GR':sorted({tuple(v) for v in classes.values()}),
         'range12_classes':sum(v==[1,2] for v in classes.values())}
    rows.append(row);print(json.dumps(row),flush=True)
assert [r['range12_classes'] for r in rows]==[0,0,1,4,1]
# Controls test actual failures, independently of the formal proofs.
t=[3,4,5,0,1,2]
controls={'wrong_euler_offset':any((3+1-boundary(t,m))%2 for m in range(64)),
          'drop_empty_circle':dart([1,0],0)-1!=boundary([1,0],0),
          'unique_at_four':rows[3]['range12_classes']!=1,
          'wrong_representative_u3':gr([1,0,3,2,5,4])!=[1,2]}
assert all(controls.values())
pathlib.Path('regression.json').write_text(json.dumps({'rows':rows,'negative_controls':controls},indent=2)+'\n')
