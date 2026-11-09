import json,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
x=json.loads((D/'extracted.json').read_text()); req=[]
for i,o in x.items():
 a=o['source_url'].rsplit('/',1)[-1];req.extend([(a+'-abs.html',o['source_url']),(a+'-html.html','https://arxiv.org/html/'+a)])
for repo,key in [('Vilin97/lean-pool','leanpool'),('openai/math','openai'),('the-omega-institute/trureturing','omega')]:req.append((key+'-head.json','https://api.github.com/repos/'+repo+'/commits/HEAD'))
(D/'outputs/requests1.json').write_text(json.dumps(req))
