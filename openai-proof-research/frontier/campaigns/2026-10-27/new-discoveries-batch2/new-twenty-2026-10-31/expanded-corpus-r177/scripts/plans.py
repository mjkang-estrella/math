import pathlib,json,re
D=pathlib.Path(__file__).resolve().parents[1]; todo=[]
for i,o in json.loads((D/'extracted.json').read_text()).items():
 a=o['source_url'].rsplit('/',1)[-1];s=(D/'sources'/f'{a}.abs.html').read_text();vs=sorted(set(re.findall(r'\[v(\d+)\]',s)),key=int);print(i,a,'versions',vs)
 todo.append([a+'.pdf','https://arxiv.org/pdf/'+a])
for a in ['2312.02933','1705.09957','2311.16390']:todo.append([a+'.pdf','https://arxiv.org/pdf/'+a])
sha=json.loads((D/'sources/leanpool-head.json').read_text())['sha']
todo[:0]=[['leanpool-tree.json',f'https://api.github.com/repos/Vilin97/lean-pool/git/trees/{sha}?recursive=1'],['projects.yml',f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/projects.yml']]
(D/'outputs/fetch2-plan.json').write_text(json.dumps(todo))
