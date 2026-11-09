import pathlib,json
P=pathlib.Path(__file__).parent;L=P.parent
for f in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 d=json.loads(f.read_text());print(f.name,str(d)[:6500])
