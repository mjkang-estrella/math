"""I171 square weights first, then minimal octagons; entirely fresh implementation."""
import json
from pathlib import Path
OWN=Path(__file__).resolve().parent
_namespace={'__file__':str(OWN/'research.py'),'__name__':'i171_research'}
exec(compile((OWN/'research.py').read_bytes(),str(OWN/'research.py'),'exec'),_namespace)
for _key,_val in _namespace.items():
    if not _key.startswith('__'):globals()[_key]=_val

def functional(rows,r):
    basis=integer_basis(rows); rr=reduce_fraction(r,rows); q=next(i for i,c in enumerate(rr) if c)
    w=[Q(0)]*len(r);w[q]=1/rr[q]
    for b in reversed(basis):
        p=next(i for i,c in enumerate(b) if c);w[p]=-sum(Q(b[j])*w[j] for j in range(p+1,len(r)))/b[p]
    assert all(sum(a*b for a,b in zip(w,z))==0 for z in rows)
    assert sum(a*b for a,b in zip(w,r))==1
    return tuple(w)

def certificate_audit(graphs,census):
    lookup={g['history']:g for g in graphs['bfs'].values()};result=[]
    certificates=read('frontier/experiments/i170_quadrilateral_coefficient/refuted-proposals.json')['proposals'][1]['certificates']
    for i,cert in zip((263,272,431),certificates):
        src=census[i];g=lookup[src['parent_history']];row,d=analyze(g,src['step'])
        assert tuple(map(tuple,cert['edges']))==d['edges']
        assert cert['faces']==g['faces'] and cert['step']==src['step']
        for name,cl in cert['classes'].items():assert {vec(tuple(map(tuple,c)),d['edges']) for c in cl}==set(d['cv'][name])
        w=cert['weight'];v=cert['old_difference']
        assert all(sum(a*b for a,b in zip(w,z))==0 for z in d['U'])
        assert sum(a*b for a,b in zip(w,v))==cert['pairing']!=0
        assert tuple(v) in {sub(a,b) for a in d['cv']['N00'] for b in d['cv']['N00']}
        row['index']=i;row['classes_exact']=True;row['separator_dot']=cert['pairing'];result.append(row)
    return result

def weights(row,d):
    if 'alpha' not in row or row['alpha']=='outside-parent-span':return None
    r=sub(d['cv']['N00'][0],d['C0']);w=functional(d['L']+d['V'],r)
    dot=lambda z:sum(a*b for a,b in zip(w,z))
    assert all(dot(sub(n,d['C0']))==1 for n in d['cv']['N00'])
    assert all(dot(sub(n,d['C0']))==0 for name in ('N10','N01','N11') for n in d['cv'][name])
    counts=Counter(str(dot(sub(vec(c,d['edges']),d['C0']))) for c in d['twofactors'])
    return {'w':list(map(str,w)),'twofactor_weight_histogram':dict(sorted(counts.items())), 'twofactors':len(d['twofactors'])}

def attack(mode):
    graphs,census=inputs();first=mandatory(graphs,census)
    if mode=='certificates':return {'first':first,'certificates':certificate_audit(graphs,census),'verdict':'PASS'}
    if mode=='weights':
        chosen=[g for g in graphs['walks'].values() if g['n']==32]
        rows=[];examples=[]
        for g in chosen:
            for step in steps(g,4):
                row,d=analyze(g,step,residual=False);row['history']=g['history']
                if 'alpha' in row:
                    detail=weights(row,d);row['weight_certificate']=detail
                    if row['alpha']=='-3/2':examples.append({'graph':g,'row':row})
                rows.append(row)
        hist=dict(sorted(Counter(r['alpha'] for r in rows if 'alpha' in r).items()))
        return {'first':first,'parents':len(chosen),'steps':len(rows),'order':32,'rows':rows,'alpha_histogram':hist,'counterexamples':examples,'shape_failures':[r for r in rows if 'shape_m' in r and (r['shape_m']=='infinite' or Q(r['shape_m']).denominator!=1 or Q(r['shape_m'])<=0)]}
    if mode=='octagons':
        chosen=list(graphs['bfs'].values())+[g for g in graphs['walks'].values() if g['n']<=32]
        rows=[];failures=[]
        for number,g in enumerate(chosen):
            for step in steps(g,8):
                terminals,A,B=boundary(g,step)
                if len(A)!=4 or len(B)!=4:continue
                row,d=analyze(g,step);row['history']=g['history'];row['parent_record']=number
                if row['t']<=row['ell']-2:failures.append({'graph':g,'row':row})
                rows.append(row)
        hist=dict(sorted(Counter(str(tuple(r[z] for z in ('ell','t','eta'))) for r in rows).items()))
        deficits=dict(sorted(Counter(str(tuple(r.get(z,0) for z in ('delta_V','delta_R','epsilon'))) for r in rows).items()))
        return {'first':first,'parent_records':len(chosen),'steps':len(rows),'rows':rows,'histogram':hist,'deficit_histogram':deficits,'counterexamples':failures}
    raise ValueError(mode)

if __name__=='__main__':
    import sys
    print(json.dumps(attack(sys.argv[1]),indent=2,sort_keys=True))
