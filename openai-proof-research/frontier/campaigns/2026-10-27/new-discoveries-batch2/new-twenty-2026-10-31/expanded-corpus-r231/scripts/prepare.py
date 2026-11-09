import json,pathlib,hashlib
D=pathlib.Path(__file__).resolve().parents[1];C=D.parent
for p in [C/'ledger.json',C.parent/'ledger.json',C.parent/'prior-campaign-context.json']:
 o=json.loads(p.read_text());(D/'logs'/('inherited-'+p.name+('-old' if p.parent==C.parent else '')+'.json')).write_text(json.dumps({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'data':o},indent=2)+'\n')
x=json.loads((D/'extracted.json').read_text());todo=[]
for o in x.values():
 a=o['source_url'].rsplit('/',1)[-1];todo.extend([(a+'-abs.html',o['source_url']),(a+'.pdf','https://arxiv.org/pdf/'+a)])
for repo in ['openai/math','Vilin97/lean-pool','the-omega-institute/trureturing']:
 todo.append((repo.replace('/','-')+'-head.json','https://api.github.com/repos/'+repo+'/commits/HEAD'))
(D/'fetch-plan.json').write_text(json.dumps(todo,indent=2)+'\n')
