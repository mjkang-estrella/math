import pathlib,json
P=pathlib.Path(__file__).parent;L=P.parent
j=lambda p:json.loads(p.read_text())
ids={x['mathdb_id'] for x in j(P/'dispositions.json')}
a=j(L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json');hist=j(L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json');ledger=j(L.parent/'ledger.json');prior=j(L.parent/'prior-campaign-context.json')
# No adjacent unassigned mathematical text: compare IDs, disclose only relevant records.
hits=[]
def visit(o,path):
 if isinstance(o,dict):
  if o.get('mathdb_id') in ids:hits.append({'path':path,'entry':o})
  for k,v in o.items():visit(v,path+'/'+k)
 elif isinstance(o,list):
  for k,v in enumerate(o):visit(v,path+'/'+str(k))
for n,o in [('accepted',a),('history',hist),('ledger',ledger),('prior',prior)]:visit(o,n)
out={'accepted_families':a['accepted_family_count'],'first_published':a['first_thirty_publication_count'],'assigned_id_hits':hits,'ledger_top_level_fields':list(ledger),'prior_top_level_fields':list(prior),'r363_decision_read':True,'adjudications_read':True,'hypothesis_queue_read':True,'limitations':'Earlier combined context displays were oversized and truncated, including unneeded historical summaries; no upstream code executed. Exact relevant assigned scientific literals were subsequently reread separately.'}
(P/'context-checks.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
f=j(P/'failures.json');f['limitations'].append(out['limitations']);(P/'failures.json').write_text(json.dumps(f,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(out,ensure_ascii=False))
