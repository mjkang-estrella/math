"""Bounded attack on equality coefficients; parent cycles enumerated freshly."""
import json
from fractions import Fraction
from collections import Counter

def one(C,es,lab,hc):
    u,v,x,y=lab[:4];e=C.edge(u,v);f=C.edge(x,y);a=C.edge(u,x);c=C.edge(v,y)
    S=[C.vec(es,z) for z in hc if e in z or f in z];N=[C.vec(es,z) for z in hc if e not in z and f not in z]
    assert S and N
    L=C.diff(S);V=C.diff(N);W=L+V;rr=C.add(N[0],C.scale(-1,S[0]));ss=C.add(C.vec(es,[e,f]),C.scale(-1,C.vec(es,[a,c])))
    dl=C.rank(L);dw=C.rank(W);dg=C.rank(W+[rr]);ell=dg-dl;t=dw-dl
    if dg==dw:return {'ell':ell,'t':t,'alpha':None}
    assert dg==dw+1
    vr=C.reducev(rr,W);vs=C.reducev(ss,W);ii=next(i for i,z in enumerate(vr) if z)
    al=vs[ii]/vr[ii]
    if any(x!=al*y for x,y in zip(vs,vr)):al=None
    assert C.rank(W+[ss])==dw+(al!=0)
    return {'ell':ell,'t':t,'alpha':str(al) if al is not None else 'outside parent span','shape_m':str(1/(1+al)) if al is not None and al!=-1 else None,'cancellation':al==Fraction(-3,2)}

def run(C,root):
    # All mandatory instances come first, even before a proposal is scanned.
    src=json.loads((root/'frontier/experiments/i169_bridge_independence/audit-attempt-02.json').read_text())['rows']
    mandatory=[0,520,522,524,527,528,530,533,534,536,539];first=[]
    for i in mandatory:
        o=src[i];es=C.canon(o['parent_edges']);hc=C.walks(es);assert hc==C.factors(es)
        ans=one(C,es,o['labels'],hc);assert ans['alpha'] in ['-1/2','-7/8'];first.append({'index':i,**ans})
    pool=json.loads((root/'frontier/experiments/i166_affine_span_braces/bracegen-graphs.json').read_text())['walks']
    gs=sorted([g for g in pool.values() if g['n']<=28],key=lambda g:(g['n'],g['history']))
    rows=[];ah=Counter();fail=[]
    for g in gs:
        es=C.canon(g['edges']);C.admissible(es,g['faces']);hc=C.walks(es);assert hc==C.factors(es)
        for fi,face in enumerate(g['faces']):
            if len(face)!=4:continue
            for i in (0,1):
                child,fs,lab=C.expand(es,g['faces'],(fi,i,i+2));C.admissible(child,fs)
                ans=one(C,es,lab,hc);row={'history':g['history'],'n':g['n'],'step':[fi,i,i+2],**ans};rows.append(row)
                if ans['alpha'] is not None:
                    ah[ans['alpha']]+=1
                    if ans['shape_m'] is not None and (Fraction(ans['shape_m']).denominator!=1 or Fraction(ans['shape_m'])<1):
                        fail.append({**row,'edges':es,'faces':g['faces'],'cycles':hc})
    return {'mandatory_first':first,'graph_limit':28,'parents':len(gs),'steps':len(rows),'histogram':dict(sorted(ah.items())),'shape_failures':fail,'rows':rows,'conclusion':'finite evidence only; no universal coefficient inference'}
