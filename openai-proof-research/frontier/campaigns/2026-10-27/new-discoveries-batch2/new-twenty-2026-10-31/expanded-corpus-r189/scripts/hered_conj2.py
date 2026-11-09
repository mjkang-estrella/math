import json,sys,pathlib,collections
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from hered import gamma,gamma_e
S=pathlib.Path(sys.argv[1]); c=collections.Counter(); allg=[]
for n in range(2,10):
    f=S/f'level-{n}.json'
    L=json.loads(f.read_text())['minimal_forbidden'] if f.exists() else json.loads((S/f'level-{n}-forbidden-merged.json').read_text())
    for adj in L:
        g=gamma(adj,n); ge=gamma_e(adj,n,g); c[(n,g,ge)]+=1; allg.append({'n':n,'adj':adj,'gamma':g,'gamma_e':ge})
(S/'minimal-forbidden-through-9.json').write_text(json.dumps(allg))
print('(order, gamma, gamma_e): count', dict(c), 'total', len(allg))
