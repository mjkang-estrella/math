from pathlib import Path
import urllib.request,hashlib,json,subprocess,datetime
L=Path(__file__).resolve().parent;url='https://arxiv.org/pdf/1903.03504v1'
try:
 with urllib.request.urlopen(url,timeout=30) as r:data=r.read(10000000)
 p=L/'new-sources/thin.pdf';p.write_bytes(data);q=L/'frozen/new-sources/thin.pdf';q.write_bytes(data)
 h=hashlib.sha256(data).hexdigest();assert hashlib.sha256(q.read_bytes()).hexdigest()==h
 rows=json.loads((L/'bindings.json').read_text());rows.append({'original':str(p),'copy':str(q.relative_to(L)),'sha256':h});(L/'bindings.json').write_text(json.dumps(rows,indent=2))
 subprocess.run(['pdftotext',str(q),str(q.with_suffix('.txt'))],check=True)
 (L/'thin-retrieval.json').write_text(json.dumps({'url':url,'sha256':h,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':200},indent=2));print(h)
except Exception as e:
 (L/'thin-fetch-failure.txt').write_text(repr(e)+'; no retry');print(repr(e))
