"""Independent I169 audit. Ancestor JSON is input data, never code."""
import json,hashlib
from collections import Counter
from pathlib import Path

def run(C,root):
    old=json.loads((root/'frontier/experiments/i169_bridge_independence/audit-attempt-02.json').read_text())
    original=json.loads((root/'frontier/experiments/i167_exchange_step_braces/diagnostic-attempt-01.json').read_text())['expansions']
    pool=json.loads((root/'frontier/experiments/i166_affine_span_braces/bracegen-graphs.json').read_text())['bfs']
    gs={g['history']:g for g in pool.values()}
    mandatory=[0,520,522,524,527,528,530,533,534,536,539]
    order=mandatory+[i for i in range(len(original)) if i not in mandatory]
    results=[];hist=Counter();sh=Counter();ah=Counter();parents=set()
    for i in order:
        oo=original[i];g=gs[oo['parent_history']];es=C.canon(g['edges']);faces=g['faces']
        if g['history'] not in parents:C.admissible(es,faces);parents.add(g['history'])
        child,cf,lab=C.expand(es,faces,oo['step']);C.admissible(child,cf)
        cl=C.classes(es,lab);lift=C.lifts(cl,lab)
        hc=C.walks(child);assert hc==C.factors(child)
        assert tuple(sorted(z for zs in lift.values() for z in zs))==hc
        # Check each of the six P4 forcing arguments on ALL child cycles containing it.
        u,v,x,y,p,q,r,s=lab
        forcing=[('N10',[p,r,s,q]),('N01',[r,p,q,s]),('Pux',[p,q,s,r]),('Pvy',[q,p,r,s]),('D11',[u,p,r,x]),('N11',[u,p,q,v])]
        for k,path in forcing:
            want=set(C.canon(zip(path,path[1:])));found=[h for h in hc if want<=set(h)]
            assert found and set(found)<=set(lift[k])
        ans,state=C.compute(es,lab,cl,child);ans['index']=i;ans['face_length']=len(faces[oo['step'][0]])
        prior=old['rows'][i];assert prior['index']==i
        assert es==C.canon(prior['parent_edges']) and child==C.canon(prior['child_edges']) and tuple(prior['labels'])==lab
        assert all(tuple(cl[k])==tuple(C.canon(z) for z in prior['classes'][k]) for k in cl)
        for k,kk in [('dg','dg'),('dh','dh'),('ell','l'),('t','t'),('eta','eta')]:assert ans[k]==prior[kk]
        assert ans['dg']==oo['d_parent'] and ans['dh']==oo['d_child'] and ans['L']==oo['d_survival'] and ans['counts']==oo['counts']
        triple=str((ans['ell'],ans['t'],ans['eta']));hist[triple]+=1
        if ans['face_length']==4:
            sq=C.square(es,lab,cl,state,ans);ans['square']=sq;sh[triple]+=1
            if sq['alpha'] is not None:ah[sq['alpha']]+=1
        ans['classes_sha256']=hashlib.sha256(json.dumps(cl,sort_keys=True).encode()).hexdigest()
        if i==0:assert (ans['ell'],ans['t'],ans['eta'])==(1,0,1)
        if i in mandatory[1:]:assert (ans['ell'],ans['t'],ans['eta'])==(7,6,1)
        results.append(ans)
    assert len(results)==636 and sum(sh.values())==206
    assert dict(ah)=={'-1/2':72,'-3/4':20,'-5/6':28,'-7/8':62}
    return {'first_tests':mandatory,'parents':len(parents),'steps':len(results),'histogram':dict(sorted(hist.items())),'square_histogram':dict(sorted(sh.items())),'alpha_histogram':dict(sorted(ah.items())),'verdicts':{'F169':'PASS ORIGINAL','S169':'PASS ORIGINAL','206_steps_and_alpha_histogram':'PASS ORIGINAL'},'rows':results}
