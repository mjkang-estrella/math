import json
from collections import Counter

def run(C,root):
    old=json.loads((root/'frontier/experiments/i169_bridge_independence/audit-attempt-02.json').read_text())['rows']
    mandatory=[0,520,522,524,527,528,530,533,534,536,539];first=[]
    for i in mandatory:
        o=old[i];es=C.canon(o['parent_edges']);cl=C.classes(es,o['labels']);ans,_=C.compute(es,o['labels'],cl,C.canon(o['child_edges']))
        assert (ans['ell'],ans['t'],ans['eta'])==((1,0,1) if i==0 else (7,6,1));first.append({'index':i,'ell':ans['ell'],'t':ans['t'],'eta':ans['eta']})
    pool=json.loads((root/'frontier/experiments/i166_affine_span_braces/bracegen-graphs.json').read_text())['walks']
    gs=sorted([g for g in pool.values() if g['n']<=24],key=lambda g:(g['n'],g['history']))
    rows=[];fails=[];hist=Counter()
    for g in gs:
        es=C.canon(g['edges']);C.admissible(es,g['faces'])
        for fi,face in enumerate(g['faces']):
            if len(face)<6:continue
            for i in range(len(face)):
                for j in range(i+2,len(face),2):
                    child,fs,lab=C.expand(es,g['faces'],(fi,i,j));C.admissible(child,fs)
                    cl=C.classes(es,lab);ans,_=C.compute(es,lab,cl,child)
                    z={'history':g['history'],'n':g['n'],'face_length':len(face),'step':[fi,i,j],'ell':ans['ell'],'t':ans['t'],'eta':ans['eta']};rows.append(z)
                    hist[str((len(face),ans['ell'],ans['t'],ans['eta']))]+=1
                    if ans['t']<=ans['ell']-2:
                        assert C.walks(child)==C.factors(child)
                        fails.append({**z,'edges':es,'faces':g['faces'],'classes':cl,'ranks':ans})
    return {'first_tests':first,'graph_limit':24,'parents':len(gs),'steps':len(rows),'failures':fails,'histogram':dict(sorted(hist.items())),'rows':rows}
