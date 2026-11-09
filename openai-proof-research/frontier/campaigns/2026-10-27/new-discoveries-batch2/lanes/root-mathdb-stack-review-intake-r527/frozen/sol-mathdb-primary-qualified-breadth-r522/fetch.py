import urllib.request,hashlib,json,datetime,pathlib
P=pathlib.Path(__file__).resolve().parent
out=[]
for ar in ['2410.17057v1','2412.17391v1','2410.06148v1','2502.02826v1','2501.03234v1']:
 url='https://arxiv.org/html/'+ar;entry={'url':url,'version':ar,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research statement screening; public primary HTML'}),timeout=25) as r:
   b=r.read();entry.update(status=r.status,final_url=r.url)
  p=P/(ar+'.html');p.write_bytes(b);entry.update(path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b),body_read=False)
 except Exception as e:entry.update(error=str(e),body_read=False,retry=False)
 out.append(entry)
 (P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(entry))
