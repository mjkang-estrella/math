import itertools,json,pathlib

def orbit(f,x):
    seen=set()
    while x not in seen:
        seen.add(x); x=f[x]
    return seen

def count(f):
    todo=set(range(len(f))); n=0
    while todo:
        todo-=orbit(f,next(iter(todo))); n+=1
    return n

def matchings(xs):
    if not xs:
        yield {}; return
    a=xs[0]
    for b in xs[1:]:
        for t in matchings([x for x in xs if x!=a and x!=b]):
            yield {a:b,b:a,**t}

swaps=0
for n in range(2,8):
    for f in itertools.permutations(range(n)):
        c=count(f)
        for a in range(n):
            for b in range(a+1,n):
                g=list(f); g[a],g[b]=g[b],g[a]
                same=b in orbit(f,a)
                assert count(g)==c+(1 if same else -1)
                assert (b in orbit(g,a))!=same
                swaps+=1
inners=0
for n in range(1,5):
    L=2*n
    for t in matchings(list(range(L))):
        for c in itertools.product((0,1),repeat=L):
            if any(c[t[i]]!=c[i] for i in range(L)): continue
            f=[]
            for h in range(3*L):
                i,r=divmod(h,3)
                j,s=(((i-1)%L,1),((i+1)%L,0),(t[i],2))[r]
                f.append(3*j+((2,0,1) if c[j] else (1,2,0))[s])
            for a in range(L):
                b=t[a]
                if a>=b or any(c[i]==c[a] for i in range(a+1,b)): continue
                assert 3*b+2 not in orbit(f,3*a+2)
                selected=({3*a+2}|{3*i for i in range(a+1,b+1)}) if not c[a] else ({3*b+2}|{3*i+1 for i in range(a,b)})
                assert {f[x] for x in selected}==selected
                inners+=1
out={'permutation_swaps':swaps,'innermost_faces':inners,'numerical_only':True}
pathlib.Path('regression6.json').write_text(json.dumps(out,indent=2)+'\n')
print(out)
