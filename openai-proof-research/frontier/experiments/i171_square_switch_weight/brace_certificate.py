"""Verify 2-extendibility of the negative two-component-factor witness."""
from pathlib import Path
import json
OWN=Path(__file__).resolve().parent
scope={'__file__':str(OWN/'attack.py'),'__name__':'i171_attack'}
exec(compile((OWN/'attack.py').read_bytes(),str(OWN/'attack.py'),'exec'),scope)
for key,value in scope.items():
    if not key.startswith('__'):globals()[key]=value

def brace_certificate():
    graphs,census=inputs();first=mandatory(graphs,census)
    old=json.loads((OWN/'weight-obstruction-attempt-01.json').read_bytes())['witnesses']['two_component_forbidden_weight']
    g=old['graph'];es,vs,cs,twos=parent(g);pairs={p for p in combinations(es,2) if not set(p[0])&set(p[1])};cover={}
    for C in twos:
        M=tuple(e for e in es if e not in C)
        for pair in combinations(M,2):
            if pair in pairs and pair not in cover:cover[pair]=M
    missing=sorted(pairs-set(cover));assert not missing
    # Each complete matching is directly checked; certificate covers EVERY disjoint edge pair.
    for pair,M in cover.items():
        assert all(e in M for e in pair) and Counter(x for e in M for x in e)==Counter(vs)
    return {'first':first,'graph':g,'definition':'Every matching of cardinality two extends to a perfect matching (2-extendible bipartite brace).','pairs':len(pairs),'perfect_matchings':len(twos),'missing':missing,'extensions':[{'pair':p,'matching':cover[p]} for p in sorted(pairs)],'verdict':'PASS'}

if __name__=='__main__':print(json.dumps(brace_certificate(),sort_keys=True,indent=2))
