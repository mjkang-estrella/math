import json,pathlib,re
L=pathlib.Path(__file__).resolve().parents[1];patterns=['jacobi','petrov','balls','narayana','matchingcomplex','matching-complex','rook','spread','wreath','colorful','discriminant','gowers','nonrepetitive','posetpermut','localgirth']
out={}
for scope in ['D5','Problems']:
 o=json.loads((L/f'sources/omega-{scope}.json').read_text()); matches=[x['path'] for x in o['tree'] if any(p in x['path'].lower() for p in patterns)];out[scope]={'sha':o['sha'],'truncated':o.get('truncated'),'paths':len(o['tree']),'matches':matches}
(L/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
