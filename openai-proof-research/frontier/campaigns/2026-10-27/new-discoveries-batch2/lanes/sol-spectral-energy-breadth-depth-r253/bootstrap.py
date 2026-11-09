import pathlib,hashlib,json,shutil
B=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2')
L=pathlib.Path(__file__).parent
records=[]
for rel,kind in [('AGENTS.md','administrative'),('ledger.json','administrative'),('prior-campaign-context.json','administrative'),('lanes/sol-ternary-eighty-breadth-depth-r252/SCOUTING.md','frozen')]:
 p=B/rel; data=p.read_bytes(); h=hashlib.sha256(data).hexdigest(); q=L/kind/p.name;q.parent.mkdir(exist_ok=True);q.write_bytes(data)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h==hashlib.sha256(q.read_bytes()).hexdigest()
 records.append(dict(original=str(p),copy=str(q),sha256=h,kind=kind))
(L/'bindings.json').write_text(json.dumps(records,indent=2))
print((L/'frozen/SCOUTING.md').read_text())
for name in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((L/'administrative'/name).read_text());print(name, str(d)[:1500])
