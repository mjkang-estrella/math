from pathlib import Path
import urllib.request,json,hashlib,datetime,subprocess
R=Path(__file__).resolve().parent;P=R/'primary';log=[]
for n in ['1904.08156','2002.09151','2211.12390']:
 url='https://arxiv.org/pdf/'+n;e={'url':url,'version':'as served, body version to be checked','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=30) as f:data=f.read(5000000);e.update(status=f.status,final_url=f.url)
  p=P/(n+'.pdf');p.write_bytes(data);e.update(path=str(p),sha256=hashlib.sha256(data).hexdigest(),size=len(data));log.append(e);(R/'successor-bodies-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
  assert data.startswith(b'%PDF')
  subprocess.run(['pdftotext','-layout',str(p),str(P/(n+'.txt'))],check=True,timeout=25)
 except Exception as ex:e['failure']=str(ex);log.append(e) if e not in log else None
 print(n,e)
 (R/'successor-bodies-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
