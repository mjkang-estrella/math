"""Exact boundary-toggle residual decomposition, with lost old generators retained."""
import json
from collections import Counter

def residuals(C,es,face,step,lab,cl,state,ans):
    L,L0,U,V,b,beta,cc,vs,S=state
    fi,i,j=step;rot=face[i:]+face[:i];jj=(j-i)%len(face)
    arcA=[rot[0]]+list(reversed(rot[jj+1:]));arcB=rot[1:jj+1]
    def signed_arc(path):
        ee=[C.edge(a,b) for a,b in zip(path,path[1:])];assert len(ee)%2==1
        return tuple(sum((1 if k%2==0 else -1) for k,z in enumerate(ee) if z==e) for e in es)
    qa=signed_arc(arcA);qb=signed_arc(arcB)
    qs={'Pux':qa,'Pvy':qb,'D11':C.add(qa,qb)}
    Vgood=[];R=[];details={}
    for name,q in qs.items():
        allp=vs[name];lookup=set(allp);good=[];mapped=[]
        for n in vs['N00']:
            z=C.add(n,C.scale(-1,q))
            if z in lookup:good.append(n);mapped.append(z)
        # Reverse construction independently tests binary incidence + membership in N00.
        back=[p for p in allp if C.add(p,q) in set(vs['N00'])];assert set(back)==set(mapped)
        bad=[p for p in allp if p not in set(mapped)]
        if good:
            anchor=C.add(good[0],C.scale(-1,q));rr=[C.add(p,C.scale(-1,anchor)) for p in bad];gg=C.diff(good)
        else:
            anchor=allp[0];rr=C.diff(allp);gg=[]
        assert C.rank(C.diff(allp)+gg+rr)==C.rank(C.diff(allp))==C.rank(gg+rr)
        assert C.rank(V+gg)==C.rank(V)
        Vgood+=gg;R+=rr
        details[name]={'good_old':len(good),'residual_paths':len(bad),'good_rank':C.rank(gg),'full_rank':C.rank(C.diff(allp)),'old_V_contained':C.rank(C.diff(allp)+V)==C.rank(C.diff(allp)),'q':q,'anchor':anchor,'extra_generators':rr}
    assert C.rank(U+Vgood+R)==C.rank(U)==C.rank(Vgood+R)
    r0=C.rank(L0);rvg=C.rank(L0+Vgood);rv=C.rank(L0+V);ru=C.rank(L0+Vgood+R)
    missing=rv-rvg;recovery=ru-rvg;eps=0 if cc is None else C.rank(L0+V+[cc])-rv
    if vs['N00']:
        assert ans['ell']-ans['t']==missing+eps-recovery
    else:assert ans['ell']==0
    return {'good_space_rank':C.rank(Vgood),'missing_old':missing,'residual_gain':recovery,'offset_gain':eps,'U_contains_V':C.rank(U+V)==C.rank(U),'classes':details}

def run(C,root):
    old=json.loads((root/'frontier/experiments/i169_bridge_independence/audit-attempt-02.json').read_text())['rows']
    graphs=json.loads((root/'frontier/experiments/i166_affine_span_braces/bracegen-graphs.json').read_text())['bfs']
    gs={g['history']:g for g in graphs.values()};mandatory=[0,520,522,524,527,528,530,533,534,536,539]
    order=mandatory+[i for i in range(len(old)) if i not in mandatory]
    rows=[];hist=Counter();missingV=[];negative=[]
    for i in order:
        o=old[i];g=gs[o['history']];es=C.canon(g['edges']);step=o['step'];f=g['faces'][step[0]]
        child,cf,lab=C.expand(es,g['faces'],step);cl=C.classes(es,lab);ans,state=C.compute(es,lab,cl,child)
        rr=residuals(C,es,f,step,lab,cl,state,ans)
        z={'index':i,'face_length':len(f),'ell':ans['ell'],'t':ans['t'],'eta':ans['eta'],**rr}
        u,v,x,y=lab[:4];a=C.edge(u,x);ccross=C.edge(v,y)
        short=[]
        for cr,name,other in [(a,'Pux','Pvy'),(ccross,'Pvy','Pux')]:
            if cr in es:
                assert all(cr in n for n in cl['N00'])
                assert tuple(sorted(tuple(e for e in n if e!=cr) for n in cl['N00']))==tuple(cl[name])
                assert all(cr in p for p in cl[other])
                assert tuple(sorted(tuple(e for e in p if e!=cr) for p in cl[other]))==tuple(cl['D11'])
                assert rr['U_contains_V'] and ans['t']>=ans['ell']-1
                L,L0,U,V,b,beta,cc,vs,S=state
                rvec=C.add(vs['N00'][0],C.scale(-1,S[0]))
                zvec=C.add(vs[other][0],C.vec(es,[C.edge(u,v),C.edge(x,y)]),C.scale(-1,C.vec(es,[cr])),C.scale(-1,S[0]))
                assert not any(C.degree(es,zvec).values())
                assert C.rank(L+U+[C.add(b,C.scale(-1,rvec),C.scale(-2,zvec))])==C.rank(L+U)
                short.append(cr)
        if len(f)==6:assert short
        z['short_gap_edges']=short
        if not rr['U_contains_V']:
            L,L0,U,V,b,beta,cc,vs,S=state
            witness=next(vv for vv in V if any(C.reducev(vv,U)))
            w=C.separator(U,witness)
            z['containment_counterexample']={'edges':es,'faces':g['faces'],'step':step,'labels':lab,'classes':cl,'weight':w,'old_difference':witness,'pairing':sum(x*y for x,y in zip(w,witness)),'rank_U':C.rank(U),'rank_U_plus_V':C.rank(U+V),'graph_order':len(C.adj(es))}
        rows.append(z)
        hist[str((len(f),rr['missing_old'],rr['residual_gain'],rr['offset_gain']))]+=1
        if not rr['U_contains_V']:missingV.append(i)
        if ans['t']<=ans['ell']-2:negative.append(i)
    return {'first_tests':mandatory,'steps':len(rows),'longer_faces':sum(z['face_length']>=6 for z in rows),'U_not_containing_V':missingV,'t_le_ell_minus_2':negative,'correction_histogram':dict(sorted(hist.items())),'rows':rows}
