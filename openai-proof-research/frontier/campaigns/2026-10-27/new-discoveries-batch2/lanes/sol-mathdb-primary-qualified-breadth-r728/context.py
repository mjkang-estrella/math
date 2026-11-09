import pathlib,json
P=pathlib.Path(__file__).resolve().parent;L=P.parent
for path in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 o=json.loads(path.read_text());print(path.name, str(o)[:500] if 'r304' not in str(path) else '')
 if 'families' in o:
  for f in o['families']:print(f.get('number'),f.get('title'),f.get('scope'))
ids={x['record']['mathdb_id'] for x in json.loads((P/'literal-records.json').read_text())}
for x in json.loads((P/'literal-records.json').read_text()):print(x['record']['mathdb_id'],x['record']['title'])
