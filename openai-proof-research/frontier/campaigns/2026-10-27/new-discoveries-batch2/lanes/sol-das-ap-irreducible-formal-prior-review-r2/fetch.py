from pathlib import Path
import sys,urllib.request,datetime,json,hashlib
B=Path(__file__).resolve().parent/'retrieval';name,url=sys.argv[1:];row=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
try:
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'IndependentSourceReview/1.0'}),timeout=30) as r:
  raw=r.read(4000000);row.update(status=r.status,final_url=r.url)
 p=B/name;f=B/('frozen-'+name);p.write_bytes(raw);f.write_bytes(raw)
 h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
 assert h(p)==h(f);row.update(file=str(p),frozen=str(f),sha256=h(p),bytes=len(raw))
except Exception as e:row.update(error=repr(e))
with (B/'http.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
print(row)
