import pathlib,hashlib,json
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
S=L.parent/'sol-wide-discrete-algebraic-certificates-r277'
H=lambda b:hashlib.sha256(b).hexdigest()
refs=[S/'SCOUTING.md',S/'discovery.md',S/'source-access-bindings.json',S/'access.jsonl',S/'sources/2311.09054v2.pdf',S/'sources/2311.09054v2.txt',S/'sources/successors.xml',S/'sources/all-versions.xml',L.parent/'root-scout-r277-disposition/SCOUTING.md',L.parent/'root-scout-r277-disposition/discovery.md']
out=[]
for p in refs:
 b=p.read_bytes();out.append(dict(original=str(p),sha256=H(b),bytes=len(b),mode='immutable-reference'))
 assert H(p.read_bytes())==H(b)
(L/'bindings.json').write_text(json.dumps(out,indent=2)+'\n')
(L/'admin').mkdir(exist_ok=True)
for p in [B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B.parents[3]/'AGENTS.md']:
 if p.exists():(L/'admin'/p.name).write_bytes(p.read_bytes())
print(json.dumps(out,indent=2))
