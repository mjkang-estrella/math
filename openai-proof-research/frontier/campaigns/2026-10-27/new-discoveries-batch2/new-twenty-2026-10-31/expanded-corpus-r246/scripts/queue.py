import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1]
rs=json.loads((D/'extracted.json').read_text())
todo=[]
for a in sorted(set(x['source_url'].split('/')[-1] for x in rs.values())):
 todo.extend([(a+'.abs','https://arxiv.org/abs/'+a),(a+'.pdf','https://arxiv.org/pdf/'+a)])
for repo,name in [('openai/math','openai'),('Vilin97/lean-pool','leanpool'),('the-omega-institute/trureturing','omega')]:
 todo.append((name+'-head.json','https://api.github.com/repos/'+repo+'/commits/HEAD'))
(D/'queue.json').write_text(json.dumps(todo))
