import pathlib,json
P=pathlib.Path(__file__).resolve().parent;L=P.parent;B=L.parent
ids={x['mathdb_id'] for x in json.loads((P/'literal-records.json').read_bytes())}
a=json.loads((L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json').read_bytes());h=json.loads((L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json').read_bytes())
print('accepted families',[(x.get('name',x.get('title',x.get('family'))),x.get('mathdb_ids')) for x in a['families']]);print('lookup assigned intersections',{k:v for k,v in a['mathdb_lookup'].items() if k in set(map(str,ids))})
print('Historical disposition sections',[(k,len(v) if hasattr(v,'__len__') else None) for k,v in h.items()]);print('Historical assigned mentions',[(i,str(h).find(str(i))>=0) for i in ids if str(i) in str(h)])
for path in [B/'ledger.json',B/'prior-campaign-context.json']:
 d=json.loads(path.read_bytes());print(path.name,{k:v for k,v in d.items() if k in ['accepted_count','total_accepted_count','next_global_outcome_number','counting_standard','acceptance_gates','note']})
