"""I169 new deductions: deleted-edge elimination, square-face recovery, prisms."""
import json
from collections import Counter
from fractions import Fraction
from toolkit import *
from audit import analyze,FIRST

def run(root):
    here=root/'frontier/experiments/i169_bridge_independence'
    data=json.loads((here/'audit-attempt-02.json').read_text());graphs=json.loads((root/'frontier/experiments/i166_affine_span_braces/bracegen-graphs.json').read_text())['bfs'];byhist={g['history']:g for g in graphs.values()}
    output=[];hist=Counter();squares=[]
    for i in FIRST+[i for i in range(636) if i not in FIRST]:
        z=data['rows'][i];es=list(map(tuple,z['parent_edges']));u,v,x,y,*_=z['labels'];uv,xy=edge(u,v),edge(x,y);K=[e for e in es if e not in [uv,xy]]
        cs={k:[frozenset(map(tuple,c)) for c in cc] for k,cc in z['classes'].items()}
        surv=cs['N10']+cs['N01']+cs['N11'];L=differences(surv,es);L0=sum((differences(cs[k],es) for k in ['N10','N01','N11']),[]);U=sum((differences(cs[k],es) for k in ['Pux','Pvy','D11']),[])
        A,B,C=[vec(cs[k][0],es) for k in ['N10','N01','N11']];P,Q,D=[vec(cs[k][0],es) for k in ['Pux','Pvy','D11']]
        flat=[p+q+d+2*int(e in [uv,xy])-a-b-c for e,p,q,d,a,b,c in zip(es,P,Q,D,A,B,C)]
        assert all(flat[es.index(e)]==0 for e in [uv,xy])
        assert all(dot(a,flat)==0 for a in incidence(es))
        assert rank(L)==2+rank(L0)
        assert rank(L+U)==2+rank(L0+U)
        assert rank(L+U+[flat])==2+rank(L0+U+[flat])==z['dm']
        assert rank(L+U+[flat,z['b']])==z['dm']
        V=differences(cs['N00'],es)
        if cs['N00']:
            n0=vec(cs['N00'][0],es);c=[nn-aa-bb+cc for nn,aa,bb,cc in zip(n0,A,B,C)]
            assert all(c[es.index(e)]==0 for e in [uv,xy])
            assert z['dg']==2+rank(L0+V+[c])
        else:assert z['l']==0;c=None
        rec={'index':i,'flat_bridge':flat,'K_kernel_dimension':len(K)-rank(incidence(K)),'L0_rank':rank(L0),'L0_U_rank':rank(L0+U),'flat_gain':rank(L0+U+[flat])-rank(L0+U),'N00_offset':c}
        if z['eta']:
            w=next(w for w in nullspace(L+U,len(es)) if dot(w,z['b']))
            assert all(dot(w,vv)==0 for vv in L+U);rec['bridge_separator']={'weight':w,'bridge_pairing':dot(w,z['b'])}
        if (z['l'],z['t'],z['eta'])==(1,1,0):
            pair=None
            for key in ['Pux','Pvy','D11']:
                for obj in cs[key][1:]:
                    diff=sub(vec(obj,es),vec(cs[key][0],es))
                    if rank_integer(L+[diff])>z['ds']:
                        w=next(w for w in nullspace(L,len(es)) if dot(w,diff))
                        pair={'class':key,'first':sorted(cs[key][0]),'second':sorted(obj),'weight':w,'difference_pairing':dot(w,diff)};break
                if pair:break
            assert pair;rec['single_lost_direction_recovered_by_U']=pair
        face=byhist[z['history']]['faces'][z['step'][0]]
        if len(face)==4:
            a,cross=edge(u,x),edge(v,y);assert cs['N00']
            for key,removed in [('Pux',{a}),('Pvy',{cross}),('D11',{a,cross})]:assert set(cs[key])=={obj-removed for obj in cs['N00']}
            assert rank(L+U)==rank(L+V)==rank(L+U+V)
            assert z['t'] in [z['l'],z['l']-1]
            s=[int(e in [uv,xy])-int(e in [a,cross]) for e in es];r=sub(vec(cs['N00'][0],es),A)
            bb=[3*rr+2*ss for rr,ss in zip(r,s)]
            assert rank_integer(L+U+[sub(z['b'],bb)])==z['lu']
            sq={'index':i,'l':z['l'],'t':z['t'],'eta':z['eta']}
            if z['t']==z['l']-1:
                w=next(w for w in nullspace(L+V,len(es)) if dot(w,r))
                alpha=Fraction(dot(w,s),dot(w,r));assert rank(L+V+[[alpha.denominator*ss-alpha.numerator*rr for ss,rr in zip(s,r)]])==z['lu']
                assert alpha!=Fraction(-3,2);sq['alpha']=str(alpha);sq['bridge_coefficient']=str(3+2*alpha)
            squares.append(sq)
        hist[str((len(face),z['l'],z['t'],z['eta']))]+=1;output.append(rec)
    pr=[]
    for length in range(4,19,2):
        g=prism(length);es=g['edges'];C=[]
        for j in range(length):
            C.append(frozenset({edge(i,(i+1)%length) for i in range(length) if i!=j}|{edge(length+i,length+(i+1)%length) for i in range(length) if i!=j}|{edge(j,length+j),edge((j+1)%length,length+(j+1)%length)}))
        allcs=hamilton(es);special=[c for c in allcs if c not in C];assert len(special)==2
        s=[int(e in [edge(0,length),edge(1,length+1)])-int(e in [edge(0,1),edge(length,length+1)]) for e in es]
        # Exact integral identity: (L-2)s=(L-3)C0-sum_{j !=0}Cj+X+Y.
        rhs=[(length-3)*vec(C[0],es)[i]-sum(vec(c,es)[i] for c in C[1:])+sum(vec(c,es)[i] for c in special) for i in range(len(es))]
        assert rhs==[(length-2)*x for x in s]
        for step,kind in [([2,0,2],'rails'),([2,1,3],'rungs')]:
            z=analyze(g,step,allcs)
            expected=[1,0,1] if kind=='rails' else [length-3,length-4,1]
            assert [z['l'],z['t'],z['eta']]==expected
            assert z['dh']==length+3
            pr.append({'L':length,'type':kind,'triple':expected,'h_child':len(z['child_cycles']),'d_child':z['dh'],'alpha':str(Fraction(-(length-3),length-2)),'bridge_coefficient':str(Fraction(length,length-2))})
    return {'status':'proved conditional/local reductions; universal exchange remains open','first_test_order':FIRST,'flattened_checks':output,'square_checks':squares,'square_count':len(squares),'structural_histogram':dict(sorted(hist.items())),'prism_family_checks':pr,'candidate_failures':[{'proposal':'Deleted-edge coordinates alone certify bridge independence','status':'REFUTED as a method','reason':'rho(L)=R^2 on the cube and every one of the 636 steps; universal six-class nonemptiness proves the same for every admissible expansion.'},{'proposal':'Small-denominator scan finds every square quotient coefficient','status':'INSUFFICIENT diagnostic, not a theorem','reason':'explore01 only searched denominators 1,2,3 and returned empty lists for denominators 4,6,8; explore02 solves coefficients exactly.'}]}
