import json,pathlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;B=L.parent
if sys.argv[1]=='context':
 for path in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
  obj=json.loads(path.read_bytes());print(str(path), 'structure',list(obj)[:20] if isinstance(obj,dict) else 'list '+str(len(obj)))
 print((L/'root-mathdb-cayley-review-intake-r363/DECISION.md').read_text())
 print((L/'root-mathdb-breadth-intake-r703/adjudications.json').read_text())
else:
 a,b=map(int,sys.argv[1:]);rows=json.loads((P/'literal-records.json').read_bytes())
 for x in rows[a:b]:
  print('\nID',x['mathdb_id'],'LOC',x['corpus_chunk'],x['corpus_line']);print(x['exact_utf8_statement']);print('SOURCE',x['record']['source_url'])
