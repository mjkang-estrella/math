import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
x=json.loads((D/'extracted.json').read_text())
todo=[['leanpool-head.json','https://api.github.com/repos/Vilin97/lean-pool/commits/HEAD'],['openai-head.json','https://api.github.com/repos/openai/math/commits/HEAD'],['omega-head.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD']]
for o in x.values():
 a=o['source_url'].rsplit('/',1)[-1];todo.append([a+'.abs.html',o['source_url']])
(D/'outputs/fetch-plan.json').write_text(json.dumps(todo))
for p in [D.parent/'ledger.json',D.parent.parent/'ledger.json',D.parent.parent/'prior-campaign-context.json']:
 o=json.loads(p.read_text());print(p.name,hashlib.sha256(p.read_bytes()).hexdigest());print(json.dumps(o,ensure_ascii=False)[-2500:])
