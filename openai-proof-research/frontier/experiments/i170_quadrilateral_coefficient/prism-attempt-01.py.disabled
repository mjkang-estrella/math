from fractions import Fraction

def graph(C,L):
    t=[C.edge(i,(i+1)%L) for i in range(L)];b=[C.edge(i+L,(i+1)%L+L) for i in range(L)];r=[(i,i+L) for i in range(L)]
    es=C.canon(t+b+r);faces=[list(reversed(range(L))),list(range(L,2*L))]+[[i,(i+1)%L,(i+1)%L+L,i+L] for i in range(L)]
    Cs=[C.canon([z for k,z in enumerate(t) if k!=j]+[z for k,z in enumerate(b) if k!=j]+[r[j],r[(j+1)%L]]) for j in range(L)]
    X=C.canon(r+[t[i] for i in range(0,L,2)]+[b[i] for i in range(1,L,2)])
    Y=C.canon(r+[t[i] for i in range(1,L,2)]+[b[i] for i in range(0,L,2)])
    return es,faces,t,b,r,Cs,X,Y

def run(C,root):
    rows=[]
    for length in range(4,19,2):
        es,fs,t,b,rs,Cs,X,Y=graph(C,length);C.admissible(es,fs)
        cyc=tuple(sorted(Cs+[X,Y]));assert cyc==C.walks(es)==C.factors(es)
        lhs=C.scale(length-2,C.add(C.vec(es,[rs[0],rs[1]]),C.scale(-1,C.vec(es,[t[0],b[0]]))))
        rhs=C.add(C.scale(length-3,C.vec(es,Cs[0])),*[C.scale(-1,C.vec(es,z)) for z in Cs[1:]],C.vec(es,X),C.vec(es,Y))
        assert lhs==rhs
        assert C.rank(C.diff([C.vec(es,z) for z in cyc]))==length+1
        for typ,step in [('rails',(2,0,2)),('rungs',(2,1,3))]:
            child,cf,lab=C.expand(es,fs,step);C.admissible(child,cf)
            cl=C.classes(es,lab);assert C.walks(child)==C.factors(child)
            lift=C.lifts(cl,lab);assert tuple(sorted(z for zs in lift.values() for z in zs))==C.walks(child)
            ans,st=C.compute(es,lab,cl,child);sq=C.square(es,lab,cl,st,ans)
            assert sq['alpha']==str(-Fraction(length-3,length-2))
            assert (ans['ell'],ans['t'],ans['eta'])==((1,0,1) if typ=='rails' else (length-3,length-4,1))
            assert ans['dh']==length+3
            rows.append({'L':length,'deletion':typ,'ranks':ans,'alpha':sq['alpha'],'identity':lhs,'admissibility':'PASS all degree, color, surface, and vertex deletion checks'})
    return {'P169':'PASS ORIGINAL','lengths':list(range(4,19,2)),'rows':rows}
