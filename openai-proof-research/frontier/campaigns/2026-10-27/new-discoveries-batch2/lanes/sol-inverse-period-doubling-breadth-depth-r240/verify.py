from work import *
m=json.loads((L/'manifest.json').read_text())
prov=json.loads((L/'provenance.json').read_text());assert sha(Path(prov['guard']['path']))==prov['guard']['sha256']
assert 'manifest.json' not in m and 'verification-receipt.json' not in m
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
assert actual==set(m)
for n,h in m.items():assert sha(L/n)==h,n
bindings=[json.loads(s) for s in (L/'bindings.jsonl').read_text().splitlines()]
for r in bindings:assert sha(Path(r['copy']))==r['sha256']==sha(Path(r['original']))
r=json.loads((L/'checks-result.json').read_text());assert r['all_assertions_pass']
assert not (L/'PROOF.md').exists()
dump('verification-receipt.json',{'pass':True,'files':len(m),'source_bindings':len(bindings),'manifest_sha256':sha(L/'manifest.json'),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'byte integrity/source equality, not proof or novelty certification','counts_unchanged':[9,39,40]})
print((L/'verification-receipt.json').read_text())
