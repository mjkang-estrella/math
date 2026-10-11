"""Fresh audit; ancestor JSON is input data, never executable."""
from pathlib import Path
import json,hashlib,random
from collections import Counter
from itertools import combinations
from toolkit import *
BASE=Path(__file__).resolve().parents[3]

def read(p):return json.loads((BASE/p).read_text())
def inputs():
    seal=read('frontier/experiments/i167_exchange_step_braces/seal.json')
    invpath=BASE/'frontier/experiments/i167_exchange_step_braces/owned-files.json'
    assert hashlib.sha256(invpath.read_bytes()).hexdigest()==seal['bindings']['inventory_sha256']
    inv=json.loads(invpath.read_text())
    for name in ['diagnostic-attempt-01.json','support-attempt-01.json']:
        p='frontier/experiments/i167_exchange_step_braces/'+name
        expected=next(x['sha256'] for x in inv['files'] if x['path']==p)
        assert hashlib.sha256((BASE/p).read_bytes()).hexdigest()==expected
    gs=read('frontier/experiments/i166_affine_span_braces/bracegen-graphs.json')['bfs']
    graphs={g['history']:g for g in gs.values()}
    assert len(graphs)==15
    return graphs,read('frontier/experiments/i167_exchange_step_braces/diagnostic-attempt-01.json'),read('frontier/experiments/i167_exchange_step_braces/support-attempt-01.json')

def dual_check(faces,cs):
    es=edges(faces);inc={e:[] for e in es}
    for j,f in enumerate(faces):
        for i in range(len(f)):inc[edge(f[i-1],f[i])].append(j)
    de=[tuple(inc[e]) for e in es];vs=set(range(len(faces)));sh=[];found=[]
    def tree(s):return connected(s,de) and sum(u in s and v in s for u,v in de)==len(s)-1
    for mask in range(1,1<<(len(faces)-1)):
        s={j+1 for j in range(len(faces)-1) if mask>>j&1}
        if tree(s) and tree(vs-s):
            found.append(frozenset(e for e,(a,b) in zip(es,de) if (a in s)!=(b in s)));sh.append(s)
    assert set(found)==set(cs) and len(found)==len(cs)
    assert all(not s<t and not t<s for s,t in combinations(sh,2))
    # Independently certify the dual cut lower bound.
    assert min(sum((u in s)!=(v in s) for u,v in de) for mask in range(1,1<<(len(faces)-1)) for s in [{j+1 for j in range(len(faces)-1) if mask>>j&1}])>=3
    return {'faces':len(faces),'partitions':len(sh),'shores':sorted([sorted(s) for s in sh])}

def typed_check(witness):
    es=edges(witness['faces']);a=adj(es);u,v=witness['deleted'];aa,bb=a[u][:],a[v][:];aa.remove(v);bb.remove(u)
    blocks=[aa,bb];centers=[u,v];mapping={z:z for z in a}
    for center,block in zip(centers,blocks):
        for z in block:mapping[z]=center
    fixed={edge(u,z) for z in aa}|{edge(v,z) for z in bb};deleted=edge(u,v)
    mapping_edges={e:edge(mapping[e[0]],mapping[e[1]]) for e in es if e not in fixed|{deleted}}
    re=sorted(mapping_edges.values());assert len(set(re))==len(re) and all(x!=y for x,y in re)
    assert re==[tuple(e) for e in witness['retract_edges']]
    ports=[[{mapping_edges[e] for e in mapping_edges if z in e} for z in block] for block in blocks]
    rc=cycles(re);typed=[c for c in rc if all(len(c&p)==1 for pp in ports for p in pp)]
    avoid=[c for c in cycles(es) if deleted not in c]
    assert {frozenset(mapping_edges[e] for e in c-fixed) for c in avoid}==set(typed)
    assert len(rc)==14 and len(typed)==len(avoid)==8
    assert dim(avoid,es)==dim(typed,re)
    return {'all':len(rc),'typed':len(typed),'avoiding':len(avoid),'affine_dimension':dim(typed,re),'ports':[[[list(e) for e in sorted(p)] for p in pp] for pp in ports]}

def main():
    gs,old,support=inputs();rng=random.Random(168);census=[]
    for name,g in gs.items():
        certify(g['faces']);es=edges(g['faces']);cs=cycles(es);assert cs==cycles_matching(es)
        original=next(x for x in old['census'] if x['history']==name)
        assert (len(cs),dim(cs,es))==(original['h'],original['d'])
        census.append({'history':name,'h':len(cs),'d':dim(cs,es),'dual':dual_check(g['faces'],cs)})
    rows=[];witness=None
    # Audit the inherited campaign before any new exchange attack.
    for number,row in enumerate(old['expansions']):
        faces=gs[row['parent_history']]['faces'];fs,l,es,he,ke,nc,classes,lifts=boundary(faces,row['step']);u,v,x,y,p,q,r,s=l
        certify(fs);hc=cycles(he);assert hc==cycles_matching(he)
        lifted=[c for cl in lifts.values() for c in cl]
        assert len(lifted)==len(set(lifted)) and set(lifted)==set(hc)
        counts={k:len(a) for k,a in nc.items()};counts.update({k:len(classes[k]) for k in ['Pux','Pvy','D11']});assert counts==row['counts']
        # All coordinate unit weights plus independent reproducible signed weights.
        weights=[[int(i==j) for i in range(len(he))] for j in range(len(he))]+[[rng.randrange(-31,32) for _ in he] for _ in range(6)]
        for weight in weights:
            w=dict(zip(he,weight));get=lambda a,b:w[edge(a,b)]
            A,B,C,D=get(p,q),get(r,s),get(p,r),get(q,s);S=A+B+C+D;delta=C+D-A-B
            tu,tv,tx,ty=get(u,p),get(v,q),get(x,r),get(y,s)
            W={e:w[e] for e in ke};W[edge(u,v)]=tu+tv-A;W[edge(x,y)]=tx+ty-B
            add={'N10':S,'N01':S,'N11':2*(A+B),'Pux':tu+tx+S-C,'Pvy':tv+ty+S-D,'D11':tu+tv+tx+ty+C+D}
            for k,cl in classes.items():
                for obj,lift in zip(cl,lifts[k]):
                    ow=sum((W if k.startswith('N') else w)[e] for e in obj)
                    assert sum(w[e] for e in lift)==ow+add[k]
        surv=nc['N10']+nc['N01']+nc['N11'];trans=lifts['N10']+lifts['N01']+lifts['N11'];ds=dim(surv,es)
        assert ds==dim(trans,he)==row['d_survival']
        for c,h in zip(surv,trans):
            E,F=int(edge(u,v) in c),int(edge(x,y) in c)
            assert [int(edge(*z) in h) for z in [(u,p),(v,q),(x,r),(y,s),(p,q),(r,s),(p,r),(q,s)]]==[E,E,F,F,F,E,2-E-F,2-E-F]
        beta=len(ke)-len(adj(es))+1;pr=dim(classes['Pux'],ke);bound=beta-2+int(edge(v,y) in ke)
        assert connected(set(adj(es))-{v,y},ke)
        assert 0<=pr<=bound<beta
        assert dim(classes['Pvy'],ke)<=beta-2+int(edge(u,x) in ke)<beta
        joint=rank([r for k in ['Pux','Pvy','D11'] for r in differences(classes[k],ke)])
        dh=dim(hc,he);dg=dim(sum(nc.values(),[]),es)
        assert (dg,dh,pr,joint,beta)==(row['d_parent'],row['d_child'],row['path_rank'],row['joint_within_path_rank'],row['K_cycle_dimension'])
        rows.append({'index':number,'history':row['parent_history'],'step':row['step'],'counts':counts,'dg':dg,'dh':dh,'ds':ds,'path_rank':pr,'path_bound':bound,'joint_within':joint,'required':dg+2-ds})
        if number==0:
            w={e:int(p in e) for e in he};delta=w[edge(p,r)]+w[edge(q,s)]-w[edge(p,q)]-w[edge(r,s)]
            agg={e:w[e] for e in ke};agg[edge(u,v)]=sum(w[edge(*a)] for a in [(u,p),(p,q),(q,v)]);agg[edge(x,y)]=sum(w[edge(*a)] for a in [(x,r),(r,s),(s,y)])
            vals={k:sorted({sum(agg[e] for e in c) for c in cl}) for k,cl in nc.items()}
            assert vals['N10']==[2] and vals['N01']==[0] and delta==0 and {sum(w[e] for e in c) for c in hc}=={2}
            witness={'labels':l,'values':vals,'delta':delta,'child_weight':2,'singleton_classes':[len(classes[k]) for k in ['Pux','Pvy','D11']]}
    assert len(rows)==636
    hist=Counter(r['required'] for r in rows);assert hist=={2:138,3:441,5:34,7:13,9:10}
    return {'census':census,'expansions':rows,'cube_failure_witness':witness,'typed':typed_check(support['mccuaig_retract']),'summary':{'steps':len(rows),'required_histogram':dict(sorted(hist.items())),'verdicts':{k:'PASS ORIGINAL' for k in ['CW167','I166 failure witness','P167','transport identity','A167 and dual correspondence','typed port bijection']}}}

if __name__=='__main__':print(json.dumps(main(),sort_keys=True,indent=2))
