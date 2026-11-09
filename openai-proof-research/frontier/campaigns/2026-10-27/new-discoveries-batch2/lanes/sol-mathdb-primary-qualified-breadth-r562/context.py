import pathlib,json
P=pathlib.Path(__file__).parent;L=P.parent;B=L.parent;I=L/'root-mathdb-breadth-intake-r561'
for p in [I/'adjudications.json',I/'hypothesis-queue.json',B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-cayley-review-intake-r363'/'DECISION.md']+list(L.glob('*r304/accepted-exclusions.json'))+list(L.glob('*r304/historical-dispositions.json')):
 print('\nCONTEXT',p,'\n',p.read_text()[:18000])
rows=json.loads((P/'assigned-records.json').read_text())
for d in rows:
 if d['mathdb_id'] in [334766,335166,335167,335328,336098,336297,337557,338347,340344,340621]:print('RECORD',json.dumps(d['record'],ensure_ascii=False))
