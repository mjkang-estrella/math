import json,pathlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;B=L.parent
if sys.argv[1]=='context':
 for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md',L/'root-mathdb-breadth-intake-r519/adjudications.json',L/'root-mathdb-breadth-intake-r519/hypothesis-queue.json']:
  print('\nFILE',p,'\n',p.read_text())
else:
 a,b=map(int,sys.argv[1:]);rs=json.loads((P/'records.json').read_text())
 for i,r in enumerate(rs[a:b],a):
  print('\nINDEX',i,'ID',r['mathdb_id'],'TITLE',r['record']['title'],'SOURCE',r['record']['source_url'],'\n'+r['statement'])
