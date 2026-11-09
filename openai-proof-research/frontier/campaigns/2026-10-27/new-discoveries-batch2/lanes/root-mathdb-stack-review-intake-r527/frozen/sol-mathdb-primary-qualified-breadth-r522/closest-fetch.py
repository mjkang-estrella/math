import urllib.request,json,hashlib,pathlib,datetime
P=pathlib.Path(__file__).resolve().parent;url='https://arxiv.org/html/2312.11141';e={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.urlopen(url,timeout=25) as r:b=r.read();e.update(status=r.status,final_url=r.url)
 p=P/'2312.11141.html';p.write_bytes(b);e.update(path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b))
except Exception as x:e.update(error=str(x),retry=False)
(P/'closest-provenance.json').write_text(json.dumps([e],indent=2)+'\n');print(json.dumps(e))
