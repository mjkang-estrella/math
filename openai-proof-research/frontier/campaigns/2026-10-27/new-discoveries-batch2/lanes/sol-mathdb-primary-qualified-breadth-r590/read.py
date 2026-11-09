import json,pathlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r589'
for name in ['adjudications.json','hypothesis-queue.json','verification-receipt.json']: print(name,(I/name).read_text())
for p in [L/'sol-mathdb-primary-qualified-breadth-r578/failures.json',*L.glob('*r363/DECISION.md')]:print(p,p.read_text())
# Required prior context read after binding; summarize size and assigned matches, not clearance.
ids={x['record']['mathdb_id'] for x in json.loads((P/'literal-records.json').read_text())}
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 obj=json.loads(p.read_text());print('CONTEXT',p.name,'entries',len(obj),'assigned-ID literal matches',[i for i in ids if str(i) in p.read_text()])
for x in json.loads((P/'literal-records.json').read_text()):
 r=x['record'];print('\nID',r['mathdb_id'],r['title'],'\nSOURCE',r['source_url'],'\n',r['statement'])
