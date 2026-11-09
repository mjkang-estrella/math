from pathlib import Path
import urllib.request,datetime,hashlib,json
root=Path(__file__).resolve().parent
urls={'source.html':'https://arxiv.org/html/2604.14639v1','source-abs.html':'https://arxiv.org/abs/2604.14639','registry-target.md':'https://raw.githubusercontent.com/the-omega-institute/trureturing/67b4fae085cf19003a33f8027410c383b49e5046/Problems/glasby-paseman-powered-ratio-maximum.md','registry-endpoint.lean':'https://raw.githubusercontent.com/the-omega-institute/trureturing/67b4fae085cf19003a33f8027410c383b49e5046/D5/S3/AnalyticClosure/BinomialPoweredRatioMaximum.lean','successor.json':'https://zenodo.org/api/records/22542573'}
receipts=[]
for name,url in urls.items():
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as f: data=f.read();rec['status']=f.status
  (root/'sources'/name).write_bytes(data);rec.update(file='sources/'+name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
 except Exception as e: rec['error']=str(e)
 receipts.append(rec)
(root/'retrievals.json').write_text(json.dumps(receipts,indent=2)+'\n')
print(json.dumps(receipts,indent=2))
