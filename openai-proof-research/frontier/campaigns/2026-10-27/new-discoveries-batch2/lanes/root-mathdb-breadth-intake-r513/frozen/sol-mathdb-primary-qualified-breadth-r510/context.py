import json,pathlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent
for p in [L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L.parent/'ledger.json',L.parent/'prior-campaign-context.json']:
 a=json.loads(p.read_text());print(str(p),json.dumps(a,ensure_ascii=False)[:23000])
