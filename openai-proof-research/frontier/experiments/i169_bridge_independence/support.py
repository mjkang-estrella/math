"""Independent D168 and M168 checks."""
from toolkit import *
import json

def brace(es):
    a=adjacency(es);color={min(a):0};todo=[min(a)]
    while todo:
        u=todo.pop()
        for v in a[u]:
            if v in color:assert color[v]!=color[u]
            else:color[v]=1-color[u];todo.append(v)
    assert len(color)==len(a) and len(es)==len(set(es)) and all(u!=v for u,v in es)
    pm=factors(es,{v:1 for v in a});pairs=[(e,f) for e,f in combinations(es,2) if not set(e)&set(f)]
    assert all(any(e in p and f in p for p in pm) for e,f in pairs)
    return {'vertices':len(a),'perfect_matchings':len(pm),'disjoint_pairs_extendable':len(pairs)}

def run(root):
    records=[]
    for length in range(4,17,2):
        g=prism(length);validate_plane(g);es=g['edges'];cs=hamilton(es);assert cs==factor_cycles(es)
        dual=dual_shores(g);assert {c for s,c in dual}==set(cs)
        Z=set(range(2,length+2));dl=[Z-{j} for j in Z]+[{1}|{j for j in Z if j%2==par} for par in [0,1]]
        assert {frozenset(s) for s,c in dual}==set(map(frozenset,dl))
        assert len(cs)==length+2 and rank(differences(cs,es))==length+1
        ordinary=[c for s,c in dual if 1 not in s];assert len(ordinary)==length
        explicit=[]
        for j in range(length):
            e={edge(i,(i+1)%length) for i in range(length) if i!=j}|{edge(length+i,length+(i+1)%length) for i in range(length) if i!=j}|{edge(j,j+length),edge((j+1)%length,length+(j+1)%length)}
            explicit.append(frozenset(e))
        assert set(explicit)==set(ordinary)
        transfer=Counter();bounds=[]
        for (s,c),(t,d) in combinations(dual,2):
            pair=tuple(sorted([len(s-t),len(t-s)]));transfer[str(pair)]+=1
            if (1 in s)!=(1 in t):assert pair in [(1,length//2-1),(2,length//2)]
            elif 1 in s:assert pair==(length//2,length//2)
            else:assert pair==(1,1)
        for bound in range(1,length//2-1):
            rows=[];allowed=[]
            for i,j in combinations(range(len(dual)),2):
                s,c=dual[i];t,d=dual[j]
                if max(len(s-t),len(t-s))<=bound:rows.append(sub(vec(c,es),vec(d,es)));allowed.append([i,j])
            assert len(allowed)==length*(length-1)//2 and rank(rows)==length-1
            assert all(1 not in dual[i][0] and 1 not in dual[j][0] for i,j in allowed)
            bounds.append({'b':bound,'rank':rank(rows),'components':3,'allowed_pairs':len(allowed)})
        records.append({'L':length,'h':len(cs),'d':rank(differences(cs,es)),'D_list':[sorted(s) for s in dl],'transfer_histogram':dict(sorted(transfer.items())),'bounds':bounds})
    source=json.loads((root/'frontier/experiments/i167_exchange_step_braces/support-attempt-01.json').read_text())['mccuaig_retract']
    pe=sorted(set(e for f in source['faces'] for e in face_edges(f)));g={'n':16,'edges':pe,'faces':source['faces']};validate_plane(g)
    deleted=edge(*source['deleted']);a=adjacency(pe);u,v=deleted
    nu=set(a[u])-{v};nv=set(a[v])-{u};assert not (nu|{u})&(nv|{v})
    mapping={z:u for z in nu|{u}}|{z:v for z in nv|{v}}
    re=sorted({edge(mapping.get(x,x),mapping.get(y,y)) for x,y in pe if (x,y)!=deleted and mapping.get(x,x)!=mapping.get(y,y)})
    assert re==list(map(tuple,source['retract_edges']))
    ports=[{edge(0,5),edge(0,15)},{edge(2,7),edge(2,14)}]
    cs=hamilton(re);assert cs==factor_cycles(re);typed=[c for c in cs if all(len(c&p)==1 for p in ports)]
    pcs=hamilton(pe);assert pcs==factor_cycles(pe)
    avoid=[c for c in pcs if deleted not in c]
    mapped={frozenset(edge(mapping.get(x,x),mapping.get(y,y)) for x,y in c if mapping.get(x,x)!=mapping.get(y,y)) for c in avoid}
    assert mapped==set(typed)
    wdict={edge(0,2):1,edge(0,5):-1,edge(1,3):1,edge(1,5):-2,edge(2,7):-1,edge(12,13):1}
    zdict={edge(0,2):1,edge(0,9):-1,edge(2,11):-1,edge(9,11):1}
    w=[wdict.get(e,0) for e in re];z=[zdict.get(e,0) for e in re];A=incidence(re);AP=A+[[int(e in p) for e in re] for p in ports]
    assert all(dot(row,z)==0 for row in AP) and dot(w,z)==1
    assert {dot(w,vec(c,re)) for c in typed}=={-1}
    rr=[rank(A),rank(AP),rank(differences(typed,re)),rank(differences(cs,re))]
    assert rr==[11,13,5,8] and [len(cs),len(typed),len(avoid)]==[14,8,8]
    return {'D168':'PASS ORIGINAL','prisms':records,'M168':'PASS ORIGINAL','typed':{'edges':re,'typed_cycles':[sorted(c) for c in typed],'weight':w,'perturbation':z,'constant':-1,'pairing':1,'ranks':rr,'ambient':len(re)-rr[1],'parent_brace':brace(pe),'retract_brace':brace(re)}}

from collections import Counter
