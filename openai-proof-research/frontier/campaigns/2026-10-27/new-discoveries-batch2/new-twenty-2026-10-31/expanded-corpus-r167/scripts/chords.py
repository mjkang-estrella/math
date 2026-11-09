# 372835 (Radtke-Keszegh-Lauff arXiv:2601.20574 Conjecture 3): blue k-gon P with m >= k-4 red pseudolines through it.
# Inside P the red lines are pseudo-chords, pairwise crossing at most once, endpoints on distinct sides of P.
# Enumerate all pseudo-chord arrangements with m chords by incremental insertion through the dual graph
# (every arrangement arises: delete the last chord). For each, compute the minimum number k of corners
# (polygon vertices) placed on the 2m boundary arcs such that (i) every chord has its endpoints on distinct sides,
# (ii) every face incident to the boundary is supported by >= 5 pseudolines. Counterexample iff kmin <= m+4.
import sys,json,time,itertools,collections
M=int(sys.argv[1]); TL=float(sys.argv[2]) if len(sys.argv)>2 else 100
t0=time.time()
class S:  # state
    pass
def initial():
    # one chord, no seam: arcs 0,1; chord segment 2
    s=S(); s.nid=3; s.kind={0:('B',None),1:('B',None),2:('R',0)}; s.faces=[[0,2],[1,2]]; s.bnd=[('A',0),('P',0),('A',1),('P',0)]; s.m=1; return s
def clone(s):
    t=S(); t.nid=s.nid; t.kind=dict(s.kind); t.faces=[list(f) for f in s.faces]; t.bnd=list(s.bnd); t.m=s.m; return t
def new(s,k):
    i=s.nid; s.nid+=1; s.kind[i]=k; return i
def insertions(s):
    # yield new states with one more chord
    c=s.m
    for fi,f in enumerate(s.faces):
        for pos,e in enumerate(f):
            if s.kind[e][0]!='B': continue
            t=clone(s); f2=t.faces[fi]
            b1=new(t,('B',None)); b2=new(t,('B',None))
            # face ccw ... b1 [start] b2 ...; rotate so list starts with b2, ends with b1
            lst=[b2]+f2[pos+1:]+f2[:pos]+[b1]
            bi=t.bnd.index(('A',e)); t.bnd[bi:bi+1]=[('A',b1),('P',c),('A',b2)]
            del t.faces[fi]
            yield from walk(t,c,lst,set())
def walk(t,c,lst,crossed):
    # current face lst, entry between lst[-1] and lst[0]; choose exit edge among lst[1:-1]? any edge except those of chord c
    L=len(lst)
    for j in range(L):
        e=lst[j]; k=t.kind[e]
        if k[0]=='R' and (k[1]==c or k[1] in crossed): continue
        if j==0 or j==L-1:
            # exiting through the halves adjacent to entry: allowed only if not the same original edge;
            # entry halves are first/last; exiting through them would be crossing the same edge/arc again
            if k[0]=='B' and len(crossed)==0 and False: pass
        u=clone(t); x1=new(u,k); x2=new(u,k); sg=new(u,('R',c))
        A=lst[:j]+[x1,sg]; B=[x2]+lst[j+1:]+[sg]
        if k[0]=='B':
            # chord ends here; endpoints must be on boundary arcs; splitting arc e
            if j in (0,L-1) and len(crossed)==0 and False: pass
            bi=u.bnd.index(('A',e)); u.bnd[bi:bi+1]=[('A',x1),('P',c),('A',x2)]
            u.faces+= [A,B]; u.m=c+1
            yield u
        else:
            # crossing chord k[1]; find other face containing e
            gi=[i for i,g in enumerate(u.faces) if e in g]
            assert len(gi)==1, (gi,)
            g=u.faces.pop(gi[0]); q=g.index(e)
            nl=[x1]+g[q+1:]+g[:q]+[x2]
            u.faces+=[A,B]
            yield from walk(u,c,nl,crossed|{k[1]})
def analyse(s):
    m=s.m
    # merge boundary pieces not separated by an endpoint (cyclically) into one arc
    toks=s.bnd; n0=len(toks); st=[i for i,x in enumerate(toks) if x[0]=='P'][0]
    aidx={}; g=-1; prevP=True
    for d in range(1,n0+1):
        x=toks[(st+d)%n0]
        if x[0]=='P': prevP=True; continue
        if prevP: g+=1; prevP=False
        aidx[x[1]]=g
    arcs=list(range(g+1))
    faces=[]
    for f in s.faces:
        ab=sorted(set(aidx[e] for e in f if s.kind[e][0]=='B'))
        if not ab: continue
        r=sum(1 for e in f if s.kind[e][0]=='R')
        faces.append((ab,r))
    # chord constraints: positions of endpoints in bnd
    toks=s.bnd; n=len(toks); pos={}
    for i,x in enumerate(toks):
        if x[0]=='P': pos.setdefault(x[1],[]).append(i)
    chordc=[]
    for c,(p,q) in pos.items():
        side1=sorted(set(aidx[toks[i][1]] for i in range(p+1,q) if toks[i][0]=='A'))
        side2=sorted(set(aidx[toks[i%n][1]] for i in range(q+1,p+n) if toks[i%n][0]=='A'))
        chordc.append((side1,side2))
    na=len(arcs); dem=[(ab,max(0,5-len(ab)-r)) for ab,r in faces]
    lb=sum(d for _,d in dem)
    if lb>m+4: return None,lb
    # exact min by DFS over per-arc counts up to bound m+4
    best=[m+5]; j=[0]*na
    def ok_partial():
        return True
    def feasible():
        for ab,d in dem:
            if sum(j[i] for i in ab)<d: return False
        for s1,s2 in chordc:
            if sum(j[i] for i in s1)<1 or sum(j[i] for i in s2)<1: return False
        return True
    def rec(i,tot):
        if tot>=best[0]: return
        if i==na:
            if feasible(): best[0]=tot
            return
        for v in range(0,5):
            j[i]=v; rec(i+1,tot+v)
        j[i]=0
    rec(0,0)
    return (best[0] if best[0]<=m+4 else None),lb
def canon(s):
    # complete invariant of the plane map given by face lists (edge ids glued pairwise), up to rotation/reflection
    occ={}
    for fi,f in enumerate(s.faces):
        for pi,e in enumerate(f): occ.setdefault(e,[]).append((fi,pi))
    best=None
    starts=[(fi,pi) for fi,f in enumerate(s.faces) for pi,e in enumerate(f) if s.kind[e][0]=='B']
    for o in (1,-1):
        for (sf,sp) in starts:
            lab={}; flab={}; out=[]; q=[(sf,sp)]; flab[sf]=0; qi=0
            while qi<len(q):
                fi,pi=q[qi]; qi+=1; f=s.faces[fi]; L=len(f); row=[]
                for d in range(L):
                    e=f[(pi+o*d)%L]
                    if e not in lab: lab[e]=len(lab)
                    row.append((lab[e],s.kind[e][0]))
                    for (gj,pj) in occ[e]:
                        if gj!=fi and gj not in flab:
                            flab[gj]=len(flab); q.append((gj,pj))
                out.append(tuple(row))
                if best is not None and tuple(out)>best[:len(out)]: break
            t=tuple(out)
            if best is None or t<best: best=t
    return best
level=[initial()]; res=[]
for m in range(2,M+1):
    nxt=[]
    for s in level:
        for t in insertions(s):
            nxt.append(t)
            if time.time()-t0>TL: break
        if time.time()-t0>TL: break
    seen={}
    for t in nxt:
        key=canon(t)
        if key not in seen: seen[key]=t
    raw=len(nxt); level=list(seen.values())
    print('raw',raw,'distinct',len(level),flush=True)
    hits=0; lbmin=99
    for s in level:
        k,lb=analyse(s); lbmin=min(lbmin,lb)
        if k is not None:
            hits+=1
            if hits<=3: res.append({'m':m,'kmin':k,'bnd':s.bnd,'faces':[[ (s.kind[e][0],s.kind[e][1]) for e in f] for f in s.faces]})
    st=collections.Counter(); dl=99; eqt=collections.Counter()
    for s_ in level:
        B=[]; I=[]
        for f in s_.faces:
            a=len([e for e in f if s_.kind[e][0]=='B']); r=len(f)-a
            (B if a else I).append((a,r))
        # merge seam not needed (initial has none); a counts arc pieces = arcs
        D=sum(max(0,5-a-r) for a,r in B); Dl=sum(5-a-r for a,r in B)
        dl=min(dl,Dl-(m+5)); st[D-(m+5)]+=1
        if D==m+5: eqt[tuple(sorted(collections.Counter((a,r) for a,r in B).items()))]+=1
    # removability test: chord c is removable if Phi(A) >= Phi(A-c) by the edge formula
    norem=0; crit=collections.Counter()
    for s_ in level:
        fb=[any(s_.kind[e][0]=='B' for e in f) for f in s_.faces]
        occ={}
        for fi,f in enumerate(s_.faces):
            for pi,e in enumerate(f): occ.setdefault(e,[]).append((fi,pi))
        good=[]
        for c in range(m):
            es=[e for e in occ if s_.kind[e]==('R',c)]
            lhs=3; rhs=0; b2=0
            for e in es:
                (f1,p1),(f2,p2)=occ[e]
                F1=s_.faces[f1]; t=2
                for nb in (F1[p1-1],F1[(p1+1)%len(F1)]):
                    if s_.kind[nb][0]=='B': t-=1
                if fb[f1] and fb[f2]: b2+=1; lhs+=2+t
                elif fb[f1] or fb[f2]:
                    other=f2 if fb[f1] else f1; rhs+=len(s_.faces[other])-2-t
            ok = lhs<=5*b2+rhs
            good.append(ok)
        if not any(good): norem+=1
        crit[sum(good)]+=1
    print('arrangements with no removable chord',norem,'#removable chords distribution',dict(sorted(crit.items())),flush=True)
    print('D-(m+5) distribution',dict(sorted(st.items())),'min Dlin-(m+5)',dl,'equality face-type profiles',len(eqt),list(eqt.items())[:6],flush=True)
    print(json.dumps({'m':m,'states':len(level),'hits':hits,'min_lower_bound':lbmin,'m_plus_4':m+4,'secs':round(time.time()-t0,1),'complete':time.time()-t0<=TL}),flush=True)
print(json.dumps(res)[:3000])
