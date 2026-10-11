"""I168 cross-class rank decomposition; exact integer computations."""
import json
from collections import Counter
from itertools import combinations
from audit import inputs,BASE,typed_check
from toolkit import *

def split_check(graph,row,index):
    fs,l,es,he,ke,nc,classes,lifts=boundary(graph['faces'],row['step']);u,v,x,y,p,q,r,s=l
    surv=nc['N10']+nc['N01']+nc['N11'];trans=lifts['N10']+lifts['N01']+lifts['N11']
    assert surv and all(classes[k] for k in ['Pux','Pvy','D11'])
    base=vec(surv[0],es);hc=[c for cl in lifts.values() for c in cl]
    L=differences(surv,es);U=[z for k in ['Pux','Pvy','D11'] for z in differences(classes[k],es)]
    # Balanced cross-class bridge pulled back to the parent degree kernel.
    bridge=[sum(int(e in classes[k][0]) for k in ['Pux','Pvy','D11'])+(2 if e in [edge(u,v),edge(x,y)] else 0)-3*t for e,t in zip(es,base)]
    assert all(sum(z for e,z in zip(es,bridge) if a in e)==0 for a in adj(es))
    ds=rank(L);r0=rank(L+U);r1=rank(L+U+[bridge]);dh=dim(hc,he);dg=dim(sum(nc.values(),[]),es)
    assert dh==2+r1
    def pi(c):return [int(edge(u,p) in c)-int(edge(v,q) in c),int(edge(p,q) in c)-int(edge(x,r) in c)]
    images={'N10':[0,0],'N01':[0,0],'N11':[0,0],'Pux':[1,0],'Pvy':[-1,1],'D11':[0,-1]}
    assert all(pi(c)==images[k] for k,cl in lifts.items() for c in cl)
    # In the parent-full sample: exact recovery and the literal balanced barycenter.
    assert r1>=dg and dh>=dg+2
    # Test a stronger, genuinely constructive candidate: every missing N00 is
    # the K-average of one object from each new class after correcting terminals.
    # It is impossible already by removed-edge coordinates: average E=F=2/3.
    # We instead record linear span membership, not convex recovery.
    missing=differences([surv[0]]+nc['N00'],es)
    contains=rank(L+U+[bridge]+missing)==r1
    return {'index':index,'history':row['parent_history'],'step':row['step'],'dg':dg,'ds':ds,'dh':dh,'loss':dg-ds,'within_mod_transport':r0-ds,'balanced_bridge_gain':r1-r0,'recovered':r1-ds,'parent_differences_contained':contains,'class_sizes':{k:len(classes[k]) for k in ['Pux','Pvy','D11']},'bridge':bridge,'parent_edges':es,'representatives':{k:sorted(classes[k][0]) for k in ['Pux','Pvy','D11']}}

def shores(faces,cs):
    es=edges(faces);inc={e:[] for e in es}
    for j,f in enumerate(faces):
        for i in range(len(f)):inc[edge(f[i-1],f[i])].append(j)
    out=[];vs=set(range(len(faces)))
    for c in cs:
        comps=components([inc[e] for e in es if e not in c],vs);assert len(comps)==2
        out.append(next(s for s in comps if 0 not in s))
    return out

def dual_moves(faces):
    es=edges(faces);cs=cycles(es);ss=shores(faces,cs);small=[];sizes=Counter();move_edges=[]
    for i,j in combinations(range(len(cs)),2):
        ab=(len(ss[i]-ss[j]),len(ss[j]-ss[i]));assert min(ab)>=1;sizes[tuple(sorted(ab))]+=1
        if ab==(1,1):small.append(sub(vec(cs[i],es),vec(cs[j],es)));move_edges.append((i,j))
    return {'n':len(adj(es)),'h':len(cs),'d':dim(cs,es),'one_each_rank':rank(small),'one_each_components':len(components(move_edges,range(len(cs)))),'transfer_sizes':{str(k):v for k,v in sorted(sizes.items())}}

def typed_detail(w):
    # Recompute the affine hull allowed by degree and typed-port equations.
    checked=typed_check(w);re=[tuple(e) for e in w['retract_edges']];a=adj(re);cs=cycles(re)
    ports=[[set(map(tuple,p)) for p in pp] for pp in checked['ports']]
    typed=[c for c in cs if all(len(c&p)==1 for pp in ports for p in pp)]
    equations=[[int(v in e) for e in re] for v in sorted(a)]
    degree_rank=rank(equations)
    for pp in ports:equations.append([int(e in pp[0]) for e in re])
    typed_ambient=len(re)-rank(equations)
    return {**checked,'retract_dimension':dim(cs,re),'degree_ambient':len(re)-degree_rank,'typed_equation_ambient':typed_ambient,'typed_dimension':dim(typed,re),'additional_deficit':typed_ambient-dim(typed,re)}

def main():
    gs,old,support=inputs();steps=old['expansions'];mandatory=[0]+[i for i,r in enumerate(steps) if r['d_parent']+2-r['d_survival']==9];assert len(mandatory)==11
    first=[split_check(gs[steps[i]['parent_history']],steps[i],i) for i in mandatory]
    rows=first+[split_check(gs[r['parent_history']],r,i) for i,r in enumerate(steps) if i not in mandatory]
    rows.sort(key=lambda r:r['index'])
    # Route ii and iii only after route i and its mandatory tests.
    dual_first=[]
    for i in mandatory:
        fs,_=expand(gs[steps[i]['parent_history']]['faces'],steps[i]['step']);dual_first.append({'index':i,**dual_moves(fs)})
    dual_census=[{'history':name,**dual_moves(g['faces'])} for name,g in gs.items()]
    return {'mandatory_first_indices':mandatory,'rank_decomposition':rows,'dual_mandatory':dual_first,'dual_census':dual_census,'typed_witness':typed_detail(support['mccuaig_retract']), 'summary':{'histogram_loss_within_bridge':{str(k):v for k,v in sorted(Counter((r['loss'],r['within_mod_transport'],r['balanced_bridge_gain']) for r in rows).items())},'all_rank_identities':True,'all_exchange_inequalities':True,'dual_one_each_failures_census':sum(r['one_each_rank']<r['d'] for r in dual_census),'dual_one_each_failures_mandatory':sum(r['one_each_rank']<r['d'] for r in dual_first)}}

if __name__=='__main__':print(json.dumps(main(),sort_keys=True,indent=2))
