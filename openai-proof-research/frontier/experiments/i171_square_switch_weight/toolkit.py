"""I171 fresh graph, enumeration and exact linear algebra. No ancestor code used."""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations
from math import gcd, lcm
from collections import Counter

def edge(a,b): return (min(a,b),max(a,b))
def adjacency(edges, vertices=None):
    a={v:[] for v in (vertices if vertices is not None else sorted({x for e in edges for x in e}))}
    for x,y in edges: a[x].append(y); a[y].append(x)
    return {x:tuple(sorted(y)) for x,y in a.items()}

def components(edges, vertices):
    a=adjacency(edges,vertices); unseen=set(vertices); ans=[]
    while unseen:
        todo=[min(unseen)]; found=set(todo); unseen-=found
        while todo:
            for v in a[todo.pop()]:
                if v in unseen: unseen.remove(v); found.add(v); todo.append(v)
        ans.append(frozenset(found))
    return ans

@lru_cache(None)
def cycles(edges):
    """Vertex DFS, root minimum label, discard reverse traversal."""
    a=adjacency(edges); root=min(a); full=set(a); found=set()
    def go(path,seen):
        v=path[-1]
        if len(seen)==len(a):
            if root in a[v] and path[1]<v:
                found.add(tuple(sorted(edge(path[i-1],path[i]) for i in range(len(path)))))
            return
        for z in a[v]:
            if z not in seen:
                # Every still unvisited vertex must retain two possible cycle neighbours,
                # except those adjacent to the two current open ends.
                left=full-seen-{z}
                if any(not any(t in left or t in (root,z) for t in a[x]) for x in left): continue
                go(path+[z],seen|{z})
    go([root],{root})
    return tuple(sorted(found))

@lru_cache(None)
def paths(edges,vertices,start,end):
    """Independent endpoint DFS for a spanning simple path."""
    a=adjacency(edges,vertices); result=[]; required=set(vertices)
    def visit(v,left,es):
        if v==end:
            if not left: result.append(tuple(sorted(es)))
            return
        for z in a[v]:
            if z in left and (z!=end or len(left)==1): visit(z,left-{z},es+[edge(v,z)])
    visit(start,required-{start},[])
    return tuple(sorted(result))

@lru_cache(None)
def degree_sets(edges,vertices,targets):
    """Edge assignment via most constrained vertex; enumerates prescribed degrees."""
    inc={v:[] for v in vertices}
    for i,(u,v) in enumerate(edges): inc[u].append(i); inc[v].append(i)
    out=[]
    def search(status,need):
        best=None
        for v in vertices:
            free=[i for i in inc[v] if status[i]<0]; k=need[v]
            if k<0 or k>len(free): return
            if free:
                score=(min(k,len(free)-k),len(free),v)
                if best is None or score<best[0]: best=(score,v,free,k)
            elif k: return
        if best is None:
            out.append(tuple(edges[i] for i,s in enumerate(status) if s)); return
        _,v,free,k=best
        for take in combinations(free,k):
            chosen=set(take); ns=status[:]; nn=need.copy()
            for i in free:
                ns[i]=int(i in chosen)
                if ns[i]:
                    x,y=edges[i]; nn[x]-=1; nn[y]-=1
            search(ns,nn)
    search([-1]*len(edges),dict(zip(vertices,targets)))
    return tuple(sorted(out))

def cover_classes(edges,vertices,u,v,x,y):
    p=paths(edges,vertices,u,x); q=paths(edges,vertices,v,y)
    for pair,ps in [((u,x),p),((v,y),q)]:
        choices=degree_sets(edges,vertices,tuple(1 if z in pair else 2 for z in vertices))
        assert tuple(c for c in choices if len(components(c,vertices))==1)==ps
    d=[]
    choices=degree_sets(edges,vertices,tuple(1 if z in (u,v,x,y) else 2 for z in vertices))
    for c in choices:
        cc=components(c,vertices)
        if len(cc)==2 and any(u in t and v in t for t in cc) and any(x in t and y in t for t in cc): d.append(c)
    return p,q,tuple(d)

def primitive(v):
    denominator=1
    for x in v: denominator=lcm(denominator, getattr(x,"denominator",1))
    v=tuple(int(x*denominator) for x in v)
    g=0
    for x in v:g=gcd(g,x)
    if not g:return tuple(v)
    lead=next(x for x in v if x)
    if lead<0:g=-g
    return tuple(x//g for x in v)

def integer_basis(rows):
    piv={}
    for row in rows:
        v=primitive(row)
        for p,b in sorted(piv.items()):
            if v[p]:
                a,c=v[p],b[p]; v=primitive(tuple(c*x-a*y for x,y in zip(v,b)))
        if any(v):p=next(i for i,x in enumerate(v) if x); piv[p]=v
    return tuple(v for _,v in sorted(piv.items()))

def fraction_rank(rows):
    """Column elimination on transpose, Fraction normalized pivots (not integer basis)."""
    if not rows:return 0
    a=[[Q(x) for x in col] for col in zip(*rows)]
    height=len(a); width=len(a[0]); rank=0
    for j in range(width):
        k=next((i for i in range(rank,height) if a[i][j]),None)
        if k is None:continue
        a[rank],a[k]=a[k],a[rank]; pivot=a[rank][j]
        a[rank]=[x/pivot for x in a[rank]]
        for i in range(rank+1,height):
            q=a[i][j]
            if q:a[i]=[x-q*y for x,y in zip(a[i],a[rank])]
        rank+=1
        if rank==height:break
    return rank

@lru_cache(20000)
def checked_rank(rows):
    r=len(integer_basis(rows)); t=fraction_rank(rows); assert r==t,(r,t); return r

def rank(rows):return checked_rank(tuple(sorted(set(tuple(x) for x in rows if any(x)))))
def add(*rows):return tuple(map(sum,zip(*rows)))
def neg(v):return tuple(-x for x in v)
def sub(a,b):return add(a,neg(b))
def scale(a,k):return tuple(k*x for x in a)
def differences(f):return tuple(sub(x,f[0]) for x in f[1:]) if f else ()
def vec(c,edges):
    chosen=set(c); return tuple(int(e in chosen) for e in edges)

def reduce_fraction(v,rows):
    a=list(map(Q,v))
    for row in integer_basis(rows):
        p=next(i for i,x in enumerate(row) if x)
        if a[p]:
            q=a[p]/row[p]; a=[x-q*y for x,y in zip(a,row)]
    return tuple(a)

def graph_check(g):
    es=tuple(map(tuple,g['edges'])); vs=tuple(sorted({v for e in es for v in e})); a=adjacency(es)
    assert len(vs)==g['n'] and len(set(es))==len(es) and all(u<v for u,v in es)
    assert all(len(a[v])==3 for v in vs)
    color={vs[0]:0}; todo=[vs[0]]
    while todo:
        u=todo.pop()
        for v in a[u]:
            if v in color:assert color[v]!=color[u]
            else:color[v]=1-color[u];todo.append(v)
    assert len(color)==len(vs)
    for dead in combinations(vs,2):
        live=set(vs)-set(dead)
        assert len(components([e for e in es if not set(e)&set(dead)],live))==1
    darts=Counter()
    for f in g['faces']:
        assert len(f)==len(set(f))
        for i,u in enumerate(f):darts[u,f[(i+1)%len(f)]]+=1
    assert set(darts)=={(u,v) for e in es for u,v in (e,e[::-1])} and set(darts.values())=={1}
    assert len(vs)-len(es)+len(g['faces'])==2
    for v in vs:
        link=[]
        for f in g['faces']:
            if v in f:
                i=f.index(v);link.append(edge(f[i-1],f[(i+1)%len(f)]))
        assert len(link)==3 and len(components(link,a[v]))==1
    cs=cycles(es)
    all2=degree_sets(es,vs,(2,)*len(vs))
    assert tuple(c for c in all2 if len(components(c,vs))==1)==cs
    return es,vs,cs,all2

@lru_cache(None)
def parent_cache(serialized):
    import json
    return graph_check(json.loads(serialized))

def parent(g):
    import json
    return parent_cache(json.dumps(g,sort_keys=True))

def boundary(g,step):
    h,i,j=step; f=g['faces'][h]; f=f[i:]+f[:i]; j=(j-i)%len(f)
    u,v,y,x=f[0],f[1],f[j],f[j+1]
    a=[u]+list(reversed(f[j+1:])); b=f[1:j+1]
    assert (len(a)-1)%2==1 and (len(b)-1)%2==1
    return (u,v,x,y),a,b

def analyze(g,step,residual=True):
    es,vs,cs,all2=parent(g); m=len(es); zero=(0,)*m
    (u,v,x,y),arcA,arcB=boundary(g,step); e=edge(u,v); f=edge(x,y)
    k=tuple(t for t in es if t not in (e,f)); cv={}
    for i,j in [(0,0),(1,0),(0,1),(1,1)]:cv['N%d%d'%(i,j)]=tuple(vec(c,es) for c in cs if (e in c)==bool(i) and (f in c)==bool(j))
    pp=cover_classes(k,vs,u,v,x,y)
    for name,cl in zip(('Pux','Pvy','D11'),pp):cv[name]=tuple(vec(c,es) for c in cl)
    assert all(cv[name] for name in ('N10','N01','N11','Pux','Pvy','D11'))
    S=cv['N10']+cv['N01']+cv['N11']; C0=S[0]; L=differences(S); L0=sum((differences(cv[z]) for z in ('N10','N01','N11')),()); V=differences(cv['N00']); U=sum((differences(cv[z]) for z in ('Pux','Pvy','D11')),())
    b=add(cv['Pux'][0],cv['Pvy'][0],cv['D11'][0],scale(vec((e,f),es),2),scale(C0,-3))
    beta=add(cv['Pux'][0],cv['Pvy'][0],cv['D11'][0],scale(vec((e,f),es),2),neg(cv['N10'][0]),neg(cv['N01'][0]),neg(cv['N11'][0]))
    dg=rank(differences(tuple(vec(c,es) for c in cs))); dl=rank(L); lu=rank(L+U)
    ell=dg-dl;t=lu-dl; eta=rank(L+U+(b,))-lu
    assert dl==rank(L0)+2 and lu==rank(L0+U)+2 and rank(L+U+(beta,))==lu+eta
    out={'n':len(vs),'step':list(step),'face_length':len(g['faces'][step[0]]),'arcs':[len(arcA)-1,len(arcB)-1],'ell':ell,'t':t,'eta':eta,'dg':dg,'rankL':dl,'rankU':rank(U),'rankUV':rank(U+V),'counts':{z:len(q) for z,q in cv.items()}}
    short=[]
    for a,name,other in [(edge(u,x),'Pux','Pvy'),(edge(v,y),'Pvy','Pux')]:
        if a not in k:continue
        av=vec((a,),es)
        assert {sub(n,av) for n in cv['N00']}==set(cv[name])
        assert {sub(p,av) for p in cv[other]}==set(cv['D11'])
        Z=differences(cv[other]); assert rank(V+Z+U)==rank(V+Z)==rank(U)
        r=sub(cv['N00'][0],C0); z=add(cv[other][0],vec((e,f),es),neg(av),neg(C0))
        assert rank(L+U+(sub(b,add(r,scale(z,2))),))==lu
        assert t>=ell-1
        if t==ell-1: assert rank(L+U+(r,))==lu+1 and (rank(L+U+(add(r,scale(z,2)),))==lu)==(eta==0)
        short.append(list(a))
    out['short_edges']=short
    if out['face_length']==6:assert short
    if out['face_length']==4:
        assert rank(U+V)==rank(U)==rank(V)
        if t==ell-1:
            r=sub(cv['N00'][0],C0); s=sub(vec((e,f),es),vec((edge(u,x),edge(v,y)),es)); W=L+V
            rr=reduce_fraction(r,W); ss=reduce_fraction(s,W); q=next(i for i,c in enumerate(rr) if c); alpha=ss[q]/rr[q]
            if ss==scale(rr,alpha):
                assert rank(W+(sub(s,scale(r,alpha)),))==rank(W)
                assert eta==int(alpha!=Q(-3,2)); out['alpha']=str(alpha);out['weight']=str(1+alpha);out['shape_m']=str(1/(1+alpha)) if alpha!=-1 else 'infinite'
            else: out['alpha']='outside-parent-span'; assert eta==1
            switched=add(cv['N00'][0],s); selected=tuple(es[i] for i,c in enumerate(switched) if c)
            assert all(c in (0,1) for c in switched) and selected in all2 and len(components(selected,vs))==2
    if residual and cv['N00']:
        def alternating(arc):
            q=[0]*m
            for i in range(len(arc)-1):q[es.index(edge(arc[i],arc[i+1]))]+=(-1)**i
            return tuple(q)
        qa,qb=alternating(arcA),alternating(arcB); vg=(); R=(); classes={}
        if len(arcA)==len(arcB)==4:
            for N in cv['N00']:
                bits=[N[es.index(edge(arc[1],arc[2]))] for arc in (arcA,arcB)]
                for qi,indices in [(qa,(0,)),(qb,(1,)),(add(qa,qb),(0,1))]:
                    toggled=sub(N,qi);binary=all(z in (0,1) for z in toggled)
                    assert binary==all(bits[i]==0 for i in indices)
                    if binary:
                        cc=components([e for e,z in zip(es,toggled) if z],vs)
                        assert len(cc) in ((1,2) if len(indices)==1 else (2,3,4))

        for name,q in [('Pux',qa),('Pvy',qb),('D11',add(qa,qb))]:
            J=cv[name]; Fj=tuple(n for n in cv['N00'] if sub(n,q) in J)
            residuals=tuple(p for p in J if add(p,q) not in cv['N00'])
            anchor=sub(Fj[0],q) if Fj else J[0]
            ej=tuple(sub(p,anchor) for p in residuals); fj=differences(Fj); dj=differences(J)
            assert rank(fj+ej)==rank(dj)==rank(dj+fj+ej)
            vg+=fj;R+=ej
            classes[name]={'q':q,'good_count':len(Fj),'residual_count':len(residuals),'good_rank':rank(fj),'class_rank':rank(dj),'residual_rank':rank(ej)}
        assert rank(vg+R)==rank(U)==rank(U+vg+R)
        c=add(cv['N00'][0],neg(cv['N10'][0]),neg(cv['N01'][0]),cv['N11'][0])
        base=rank(L0+vg);dv=rank(L0+V)-base;dr=rank(L0+vg+R)-base;eps=rank(L0+V+(c,))-rank(L0+V)
        assert ell-t==dv+eps-dr
        assert (t+eta>=ell)==(dr+eta>=dv+eps)
        out.update(delta_V=dv,delta_R=dr,epsilon=eps,classes=classes)
    return out,{'edges':es,'vertices':vs,'cycles':cs,'twofactors':all2,'cv':cv,'L':L,'L0':L0,'U':U,'V':V,'b':b,'beta':beta,'C0':C0}

def steps(g,length=None):
    for h,face in enumerate(g['faces']):
        if length is not None and len(face)!=length:continue
        for i in range(len(face)):
            for j in range(i+2,len(face)):
                if j-i<=len(face)-2 and (j-i)%2==0:yield [h,i,j]

def expand(g,step):
    """Plane C4 expansion constructed directly from oriented boundary walks."""
    h,i,j=step; face=g['faces'][h]; rotated=face[i:]+face[:i]; offset=(j-i)%len(face)
    u,v,y,x=rotated[0],rotated[1],rotated[offset],rotated[offset+1]
    p=max(z for e in g['edges'] for z in e)+1;q=p+1;r=p+2;s=p+3
    e=edge(u,v);f=edge(x,y);es=[tuple(z) for z in g['edges'] if tuple(z) not in (e,f)]
    es+=list(map(lambda z:edge(*z),[(u,p),(v,q),(x,r),(y,s),(p,q),(q,s),(s,r),(r,p)]))
    replacements={(u,v):[u,p,q],(v,u):[v,q,p],(x,y):[x,r,s],(y,x):[y,s,r]};faces=[]
    for k,F in enumerate(g['faces']):
        if k==h:continue
        ff=[]
        for l,a in enumerate(F):ff+=replacements.get((a,F[(l+1)%len(F)]),[a])
        faces.append(ff)
    faces+=[rotated[1:offset+1]+[s,q],rotated[offset+1:]+[u,p,r],[p,q,s,r]]
    return {'n':g['n']+4,'edges':[list(z) for z in sorted(es)],'faces':faces,'history':g['history']+' I171S'+str(step)}
