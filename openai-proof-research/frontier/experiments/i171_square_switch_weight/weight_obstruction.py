"""Certify failure of generic 2-factor positivity, not of square exchange."""
from pathlib import Path
import json
OWN=Path(__file__).resolve().parent
scope={'__file__':str(OWN/'attack.py'),'__name__':'i171_attack'}
exec(compile((OWN/'attack.py').read_bytes(),str(OWN/'attack.py'),'exec'),scope)
for key,value in scope.items():
    if not key.startswith('__'):globals()[key]=value

def obstruction():
    graphs,census=inputs();first=mandatory(graphs,census)
    previous=json.loads((OWN/'weights-attempt-01.json').read_bytes());lookup={g['history']:g for g in graphs['walks'].values()}
    witnesses={};examined=0
    for saved in previous['rows']:
        if 'weight_certificate' not in saved:continue
        g=lookup[saved['history']];row,d=analyze(g,saved['step'],residual=False);examined+=1
        w=tuple(map(Q,saved['weight_certificate']['w']));dot=lambda z:sum(a*b for a,b in zip(w,z))
        assert all(dot(z)==0 for z in d['L']+d['V']) and dot(sub(d['cv']['N00'][0],d['C0']))==1
        for c in d['twofactors']:
            comps=components(c,d['vertices']);value=dot(sub(vec(c,d['edges']),d['C0']))
            if len(comps)!=2:continue
            keys=[]
            if value<0:keys.append('two_component_negative')
            if value==Q(-1,2):keys.append('two_component_forbidden_weight')
            for key in keys:
                if key not in witnesses:
                    witnesses[key]={'graph':g,'step':saved['step'],'row':row,'w':list(map(str,w)),'C0':d['C0'],'N':d['cv']['N00'][0],'factor_edges':c,'component_vertices':[sorted(t) for t in comps],'factor_weight':str(value),'specific_square_factor_weight':row['weight'],'distinction':'factor is NOT the prescribed N+s square switch'}
        if len(witnesses)==2:break
    assert witnesses
    return {'first':first,'equality_steps_examined':examined,'witnesses':witnesses,'conclusion':'Generic 2-factor positivity refuted; specific square-switch exclusion remains open.'}

if __name__=='__main__':print(json.dumps(obstruction(),sort_keys=True,indent=2))
