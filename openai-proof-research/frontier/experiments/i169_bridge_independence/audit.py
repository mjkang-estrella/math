"""Independent I168 audit. Ancestor inputs are JSON data only."""
import json
from collections import Counter
from pathlib import Path
from toolkit import *
NINE=[520,522,524,527,528,530,533,534,536,539]
MANDATORY=[0]+list(range(520,540))
FIRST=[0]+NINE+[i for i in MANDATORY if i not in [0]+NINE]

def analyze(g,step,parent=None,full=True):
    es=sorted(map(tuple,g['edges']));h,labs=expand(g,step);hs=h['edges'];u,v,x,y,p,q,r,s=labs
    uv,xy=edge(u,v),edge(x,y);K=sorted(set(es)-{uv,xy});parent=hamilton(es) if parent is None else parent
    assert parent==factor_cycles(es)
    if full:validate_plane(h)
    child=hamilton(hs);assert child==factor_cycles(hs)
    classes={'N'+str(int(uv in c))+str(int(xy in c)):[] for c in parent}
    for key in ['N00','N10','N01','N11']:classes.setdefault(key,[])
    for c in parent:classes['N'+str(int(uv in c))+str(int(xy in c))].append(c)
    classes['Pux']=hamilton(K,u,x);classes['Pvy']=hamilton(K,v,y);classes['D11']=two_paths(K,(u,v,x,y))
    assert all(classes[k] for k in ['Pux','Pvy','D11'])
    arm=[edge(u,p),edge(v,q),edge(x,r),edge(y,s)];sq=[edge(p,q),edge(r,s),edge(p,r),edge(q,s)]
    def transport(z,affine=False):
        z=dict(zip(es,z));E=z[uv];F=z[xy];d={e:z[e] for e in K}
        d.update(zip(arm,[E,E,F,F]));d.update(zip(sq,[F,E,(2 if affine else 0)-E-F,(2 if affine else 0)-E-F]))
        return [d[e] for e in hs]
    def newlift(c,key):
        aa,ss={'Pux':([1,0,1,0],[1,1,0,1]),'Pvy':([0,1,0,1],[1,1,1,0]),'D11':([1,1,1,1],[0,0,1,1])}[key]
        return frozenset(set(c)|{e for e,a in zip(arm,aa) if a}|{e for e,a in zip(sq,ss) if a})
    def pi(z):return (z[hs.index(arm[0])]-z[hs.index(arm[1])],z[hs.index(sq[0])]-z[hs.index(arm[2])])
    lifts={};surv=sorted(classes['N10']+classes['N01']+classes['N11'],key=lambda c:tuple(sorted(c)))
    for key in ['N10','N01','N11']:
        lifts[key]=[frozenset(e for e,val in zip(hs,transport(vec(c,es),True)) if val) for c in classes[key]]
    for key in ['Pux','Pvy','D11']:lifts[key]=[newlift(c,key) for c in classes[key]]
    assert set(child)==set(c for cs in lifts.values() for c in cs)
    assert sum(map(len,lifts.values()))==len(child)
    for key,cs in lifts.items():
        for c in cs:assert pi(vec(c,hs))=={'Pux':(1,0),'Pvy':(-1,1),'D11':(0,-1)}.get(key,(0,0))
    L=differences(surv,es);U=sum((differences(classes[k],es) for k in ['Pux','Pvy','D11']),[])
    c0=vec(surv[0],es);reps=[vec(classes[k][0],es) for k in ['Pux','Pvy','D11']]
    b=[sum(w[i] for w in reps)+2*int(e in [uv,xy])-3*c0[i] for i,e in enumerate(es)]
    A=incidence(es);assert all(dot(row,b)==0 for row in A)
    assert all(dot(row,z)==0 for row in A for z in L+U)
    # Full degree-kernel identification, independent of the cycle census.
    ker=nullspace(A,len(es));mapped=[transport(z) for z in ker]
    AH=incidence(hs);pr1=[int(e==arm[0])-int(e==arm[1]) for e in hs];pr2=[int(e==sq[0])-int(e==arm[2]) for e in hs]
    assert all(all(dot(row,z)==0 for row in AH+[pr1,pr2]) for z in mapped)
    assert rank(mapped)==len(es)-rank(A)==len(hs)-rank(AH+[pr1,pr2])
    # Sum of the three new lift differences pulls back exactly to b.
    base=transport(c0,True);newdiff=[sub(vec(lifts[k][0],hs),base) for k in ['Pux','Pvy','D11']]
    assert [sum(w[i] for w in newdiff) for i in range(len(hs))]==transport(b)
    # Representative changes: check the complete set of one-choice substitutions.
    lu=rank(L+U)
    for key,rep in zip(['Pux','Pvy','D11'],reps):
        for c in classes[key]:assert rank_integer(L+U+[sub(vec(c,es),rep)])==lu
    for c in surv:assert rank_integer(L+U+[sub(vec(c,es),c0)])==lu
    dg=rank(differences(parent,es));ds=rank(L);dm=rank(L+U+[b]);dh=rank(differences(child,hs))
    assert dh==2+dm
    # Actual child pi-kernel ranks; not inferred from the identity being tested.
    td=[transport(z) for z in L+U+[b]]
    assert rank(td)==dm and rank(td+newdiff)==dh
    assert rank(differences(lifts['N10']+lifts['N01']+lifts['N11'],hs))==ds
    return {'parent_edges':es,'child_edges':hs,'labels':labs,'step':step,'counts':{k:len(v) for k,v in classes.items()},'dg':dg,'dh':dh,'ds':ds,'lu':lu,'dm':dm,'l':dg-ds,'t':lu-ds,'eta':dm-lu,'b':b,'classes':{k:[sorted(c) for c in cs] for k,cs in classes.items()},'child_cycles':[sorted(c) for c in child],'projection_rank_L':rank([[z[es.index(uv)],z[es.index(xy)]] for z in L]),'parent_differences_contained':rank(L+U+[b]+differences(parent,es))==dm}

def run(root):
    exp=root/'frontier/experiments';graphs=list(json.loads((exp/'i166_affine_span_braces/bracegen-graphs.json').read_text())['bfs'].values())
    steps=json.loads((exp/'i167_exchange_step_braces/diagnostic-attempt-01.json').read_text())['expansions'];old=json.loads((exp/'i168_cross_class_exchange/attack-attempt-01.json').read_text())
    byhist={g['history']:g for g in graphs};parents={}
    for g in graphs:
        validate_plane(g);cs=hamilton(g['edges']);assert cs==factor_cycles(g['edges']);parents[g['history']]=cs
    results={}
    for i in FIRST+[i for i in range(len(steps)) if i not in FIRST]:
        st=steps[i];g=byhist[st['parent_history']];z=analyze(g,st['step'],parents[g['history']]);z['index']=i;z['history']=g['history']
        assert z['counts']==st['counts'],(i,z['counts'],st['counts'])
        assert [z['dg'],z['dh'],z['ds']]==[st['d_parent'],st['d_child'],st['d_survival']]
        o=old['rank_decomposition'][i];assert [z['l'],z['t'],z['eta']]==[o['loss'],o['within_mod_transport'],o['balanced_bridge_gain']]
        assert z['parent_differences_contained']==o['parent_differences_contained'];results[i]=z
    rows=[results[i] for i in range(len(steps))];hist=Counter(str((z['l'],z['t'],z['eta'])) for z in rows)
    expected={'(0, 0, 0)':138,'(1, 0, 1)':385,'(1, 1, 0)':56,'(3, 2, 1)':34,'(5, 4, 1)':13,'(7, 6, 1)':10}
    assert hist==expected;assert [z['index'] for z in rows if z['l']==7]==NINE
    assert old['mandatory_first_indices']==[0]+NINE
    return {'verdict':'PASS ORIGINAL','rows':rows,'histogram':dict(sorted(hist.items())),'first_test_order':FIRST,'mandatory_set':MANDATORY,'nine_direction_set':NINE,'rank_crosscheck':'Two independent exact implementations on every step and every reported rank','enumerators':'Vertex DFS versus edge degree-factor recursion; path and two-path exterior enumeration versus child cycle restriction'}

if __name__=='__main__':
    import sys
    print(json.dumps(run(Path(__file__).resolve().parents[3]),sort_keys=True,indent=2))
