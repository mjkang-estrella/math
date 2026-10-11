"""Face-preserving local search around index 431, after primary weight scan."""
from pathlib import Path
import json
OWN=Path(__file__).resolve().parent
scope={'__file__':str(OWN/'attack.py'),'__name__':'i171_attack'}
exec(compile((OWN/'attack.py').read_bytes(),str(OWN/'attack.py'),'exec'),scope)
for key,value in scope.items():
    if not key.startswith('__'):globals()[key]=value

def targeted():
    graphs,census=inputs();first=mandatory(graphs,census)
    src=census[431];g=next(g for g in graphs['bfs'].values() if g['history']==src['parent_history'])
    protected=g['faces'][src['step'][0]]; perimeter={edge(protected[i-1],protected[i]) for i in range(len(protected))}
    levels=[[g]];seen={tuple(map(tuple,g['edges']))};out=[]
    for depth in range(1,4):
        new=[]
        for prev in (levels[-1] if depth==1 else levels[-1][:6]):
            choices=[]
            for step in steps(prev,4):
                (u,v,x,y),_,_=boundary(prev,step)
                if edge(u,v) not in perimeter and edge(x,y) not in perimeter:choices.append(step)
            if depth==3:choices=choices[:4]
            for step in choices:
                child=expand(prev,step);key=tuple(map(tuple,child['edges']))
                if key in seen:continue
                seen.add(key);assert protected in child['faces'];new.append(child)
                target=[child['faces'].index(protected),0,4];row,d=analyze(child,target)
                assert row['arcs']==[3,3]
                row['depth']=depth;out.append({'graph':child,'row':row})
        levels.append(new)
    hist=dict(sorted(Counter(str(tuple(c['row'][z] for z in ('ell','t','eta'))) for c in out).items()))
    deficits=dict(sorted(Counter(str(tuple(c['row'].get(z,0) for z in ('delta_V','delta_R','epsilon'))) for c in out).items()))
    return {'first':first,'levels':[len(x) for x in levels],'records':out,'steps':len(out),'histogram':hist,'deficit_histogram':deficits,'counterexamples':[c for c in out if c['row']['t']<=c['row']['ell']-2]}

if __name__=='__main__':print(json.dumps(targeted(),sort_keys=True,indent=2))
