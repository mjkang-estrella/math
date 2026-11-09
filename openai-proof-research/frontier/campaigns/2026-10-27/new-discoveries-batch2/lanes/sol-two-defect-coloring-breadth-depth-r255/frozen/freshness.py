import pathlib,json,hashlib,re
L=pathlib.Path(__file__).parent
terms=['2103.01541','2103.05171','2103.09114','2103.10684','2103.11432','2103.11655','2103.14594','2103.14687','2104.01731','2104.05665','2104.09009','2104.09241','2104.09405','acyclic matching','Gardner','Levine','vertex.splitting','cross.product conjecture','Di Francesco']
hits={t:[] for t in terms}
for r in json.loads((L/'history-bindings.json').read_text()):
 p=pathlib.Path(r['path']);data=p.read_bytes();assert hashlib.sha256(data).hexdigest()==r['sha256'];s=data.decode(errors='replace')
 for t in terms:
  if re.search(t,s,re.I):hits[t].append(str(p))
 assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
(L/'freshness-hits.json').write_text(json.dumps(hits,indent=2));print(json.dumps(hits,indent=2))
