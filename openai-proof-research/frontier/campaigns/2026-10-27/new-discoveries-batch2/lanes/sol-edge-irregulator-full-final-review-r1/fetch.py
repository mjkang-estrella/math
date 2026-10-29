from pathlib import Path
import urllib.request,hashlib,json,datetime
r=Path(__file__).resolve().parent;h='1b999d9fda71df7537b62327147496d64a6f66ef'
paths=['D5/S3/ArithSums/A397436GeneralSupercongruenceRefutation.lean','D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.lean','docs/develop/theory/GRAPH_ENERGY_GAME_BIPARTITE_THRESHOLDS.md']
receipts=[]
for p in paths:
 u='https://raw.githubusercontent.com/the-omega-institute/trureturing/'+h+'/'+p
 try:
  with urllib.request.urlopen(u,timeout=20) as f:d=f.read();status=f.status;final=f.url
  dest=r/'fresh-bodies'/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(d)
  receipts.append({'url':u,'final_url':final,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':status,'sha256':hashlib.sha256(d).hexdigest(),'local':str(dest.relative_to(r))})
 except Exception as e:
  receipts.append({'url':u,'error':str(e),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()});break
(r/'http.json').write_text(json.dumps(receipts,indent=2))
