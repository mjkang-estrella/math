"""I168 fresh standard-library toolkit. No ancestor code imports."""
from itertools import combinations
from math import gcd

def edge(a,b): return (min(a,b),max(a,b))
def edges(faces): return sorted({edge(f[i-1],f[i]) for f in faces for i in range(len(f))})
def adj(es):
    a={v:[] for e in es for v in e}
    for u,v in es: a[u].append(v);a[v].append(u)
    return {v:sorted(ns) for v,ns in a.items()}
def connected(vs,es):
    vs=set(vs)
    if not vs: return False
    a={v:[] for v in vs}
    for u,v in es:
        if u in vs and v in vs: a[u].append(v);a[v].append(u)
    seen={min(vs)};todo=list(seen)
    while todo:
        for v in a[todo.pop()]:
            if v not in seen: seen.add(v);todo.append(v)
    return seen==vs

def certify(faces):
    es=edges(faces);a=adj(es);vs=set(a)
    assert all(len(f)==len(set(f)) for f in faces)
    darts=[(f[i-1],f[i]) for f in faces for i in range(len(f))]
    assert len(darts)==2*len(es) and len(set(darts))==len(darts)
    assert set(darts)=={(u,v) for u,v in es}|{(v,u) for u,v in es}
    assert len(vs)-len(es)+len(faces)==2
    for v in vs:
        rot={f[i-1]:f[(i+1)%len(f)] for f in faces for i in range(len(f)) if f[i]==v}
        t=min(rot);s=t;seen=set()
        while t not in seen: seen.add(t);t=rot[t]
        assert t==s and seen==set(a[v])
    assert all(len(a[v])==3 for v in vs)
    color={min(vs):0};todo=list(color)
    while todo:
        u=todo.pop()
        for v in a[u]:
            if v in color: assert color[v]!=color[u]
            else: color[v]=1-color[u];todo.append(v)
    for k in (0,1,2):
        for delete in combinations(sorted(vs),k): assert connected(vs-set(delete),es)
    return color

def cycles(es):
    a=adj(es);s=min(a);n=len(a);out=set()
    def visit(v,seen,path):
        if len(seen)==n:
            if s in a[v] and path[1]<v:
                out.add(frozenset(edge(path[i-1],path[i]) for i in range(n)))
            return
        for w in a[v]:
            if w not in seen: visit(w,seen|{w},path+[w])
    visit(s,{s},[s]);return sorted(out,key=lambda c:sorted(c))

def matchings(es,vertices=None):
    a=adj(es);vs=set(a) if vertices is None else set(vertices)
    def rec(left,chosen):
        if not left: yield frozenset(chosen);return
        u=min(left,key=lambda v:(len(set(a.get(v,()))&left),v))
        for v in a.get(u,()):
            if v in left: yield from rec(left-{u,v},chosen+[edge(u,v)])
    return list(rec(vs,[]))

def cycles_matching(es):
    vs=set(adj(es));universe=set(es)
    return sorted([frozenset(universe-m) for m in matchings(es) if connected(vs,universe-m)],key=lambda c:sorted(c))

def paths(es,s,t):
    a=adj(es);n=len(a);out=[]
    def rec(v,seen,used):
        if v==t:
            if len(seen)==n: out.append(frozenset(used))
            return
        for w in a[v]:
            if w not in seen: rec(w,seen|{w},used+[edge(v,w)])
    rec(s,{s},[]);return sorted(out,key=lambda c:sorted(c))

def components(es,vs):
    a={v:[] for v in vs}
    for u,v in es: a[u].append(v);a[v].append(u)
    left=set(vs);out=[]
    while left:
        comp={min(left)};todo=list(comp);left-=comp
        while todo:
            for v in a[todo.pop()]:
                if v in left: left.remove(v);comp.add(v);todo.append(v)
        out.append(comp)
    return out

def covers(es,u,v,x,y):
    vs=set(adj(es));out=[];cross=[]
    for m in matchings(es):
        d=frozenset(set(es)-m);cs=components(d,vs)
        if len(cs)!=2: continue
        if all(len(set((u,v,x,y))&c)==2 for c in cs):
            if any({u,v}<=c for c in cs): out.append(d)
            if any({u,y}<=c for c in cs): cross.append(d)
    return sorted(out,key=lambda c:sorted(c)),cross

def vec(c,es): return [int(e in c) for e in es]
def sub(a,b):return [x-y for x,y in zip(a,b)]
def rank(rows):
    piv={}
    for r in rows:
        r=list(r)
        for j in sorted(piv):
            if r[j]:
                p=piv[j];a=r[j];b=p[j];r=[b*x-a*y for x,y in zip(r,p)]
                g=0
                for x in r: g=gcd(g,x)
                if g>1:r=[x//g for x in r]
        j=next((j for j,x in enumerate(r) if x),None)
        if j is not None:
            g=0
            for x in r:g=gcd(g,x)
            if r[j]<0:g=-g
            piv[j]=[x//g for x in r]
    return len(piv)
def differences(cs,es):
    if not cs:return []
    v=vec(cs[0],es);return [sub(vec(c,es),v) for c in cs[1:]]
def dim(cs,es):return rank(differences(cs,es)) if cs else -1

def expand(faces,step):
    fi,i,j=step;f=faces[fi];u,v=f[i],f[(i+1)%len(f)];y,x=f[j],f[(j+1)%len(f)]
    p=max(v for f in faces for v in f)+1;q,r,s=p+1,p+2,p+3
    replace={(u,v):[p,q],(v,u):[q,p],(x,y):[r,s],(y,x):[s,r]}
    fs=[]
    for k,ff in enumerate(faces):
        if k==fi:continue
        nf=[]
        for a,b in zip(ff,ff[1:]+ff[:1]):nf += [a]+replace.get((a,b),[])
        fs.append(nf)
    fs += [f[i+1:j+1]+[s,q], f[j+1:]+f[:i+1]+[p,r], [p,q,s,r]]
    return fs,(u,v,x,y,p,q,r,s)

def boundary(faces,step):
    fs,l=expand(faces,step);u,v,x,y,p,q,r,s=l;es=edges(faces);he=edges(fs);e=edge(u,v);f=edge(x,y);ke=sorted(set(es)-{e,f})
    nc={k:[] for k in ['N00','N10','N01','N11']}
    for c in cycles(es):nc['N'+str(int(e in c))+str(int(f in c))].append(c)
    pu=paths(ke,u,x);pv=paths(ke,v,y);ds,cross=covers(ke,u,v,x,y);assert not cross
    classes={k:cs for k,cs in nc.items() if k!='N00'};classes.update(Pux=pu,Pvy=pv,D11=ds)
    fixed={
       'N10':[(u,p),(v,q),(r,s),(p,r),(q,s)],
       'N01':[(x,r),(y,s),(p,q),(p,r),(q,s)],
       'N11':[(u,p),(v,q),(x,r),(y,s),(p,q),(r,s)],
       'Pux':[(u,p),(x,r),(p,q),(r,s),(q,s)],
       'Pvy':[(v,q),(y,s),(p,q),(r,s),(p,r)],
       'D11':[(u,p),(v,q),(x,r),(y,s),(p,r),(q,s)]}
    lifts={k:[frozenset((set(c)-{e,f})|{edge(*a) for a in fixed[k]}) for c in cs] for k,cs in classes.items()}
    return fs,l,es,he,ke,nc,classes,lifts
