"""Retained structural diagnosis of mandatory index 431; no containment premise."""
import json
from pathlib import Path
OWN=Path(__file__).resolve().parent
scope={'__file__':str(OWN/'attack.py'),'__name__':'i171_attack'}
exec(compile((OWN/'attack.py').read_bytes(),str(OWN/'attack.py'),'exec'),scope)
for key,value in scope.items():
    if not key.startswith('__'):globals()[key]=value

def guide():
    graphs,census=inputs();first=mandatory(graphs,census);src=census[431];g=next(g for g in graphs['bfs'].values() if g['history']==src['parent_history']);row,d=analyze(g,src['step']);term,A,B=boundary(g,src['step']);records=[]
    for N in d['cv']['N00']:
        rec={'cycle':[list(e) for e,z in zip(d['edges'],N) if z],'middle_bits':[N[d['edges'].index(edge(arc[1],arc[2]))] for arc in (A,B)],'toggles':{}}
        for name,cl in row['classes'].items():
            toggled=sub(N,cl['q']);bad=[i for i,z in enumerate(toggled) if z not in (0,1)]
            rec['toggles'][name]={'non_binary_coordinates':bad,'component_vertices':[] if bad else [sorted(c) for c in components([e for e,z in zip(d['edges'],toggled) if z],d['vertices'])]}
        records.append(rec)
    # A normalized bridge separator annihilating all of L+U; different from I170's U-only separator.
    w=functional(d['L']+d['U'],d['b']);dot=lambda v:sum(a*b for a,b in zip(w,v))
    assert dot(d['b'])==1 and all(dot(z)==0 for z in d['L']+d['U'])
    factor=1
    for a in w:factor=lcm(factor,a.denominator)
    iw=tuple(int(a*factor) for a in w)
    return {'first':first,'graph':g,'row':row,'arcs':[A,B],'old_cycles':records,'bridge_separator':{'w':iw,'b':d['b'],'dot':factor,'L_and_U_zero':True},'old_difference_bridge_weights':[str(dot(v)) for v in d['V']]}

if __name__=='__main__':print(json.dumps(guide(),sort_keys=True,indent=2))
