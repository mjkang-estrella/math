exec((__import__('pathlib').Path(__file__).parent/'prepare.py').read_text())
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json',I/'adjudications.json',I/'hypothesis-queue.json']:
 print(p.name,p.read_text()[:16000])
for p in [L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 z=load(p);print(p.name,'type',type(z).__name__,'keys',list(z)[:15] if isinstance(z,dict) else len(z))
for p in refs:
 if 'r363' in p:print(p,pathlib.Path(p).read_text()[:8000])
