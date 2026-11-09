import pathlib,json,hashlib,urllib.request,datetime,subprocess
P=pathlib.Path(__file__).parent
out=[]
for id,arx in [(325680,'1306.0136v1'),(326550,'1310.5172v1'),(326814,'1312.2195v1')]:
 url='https://arxiv.org/pdf/'+arx;a={'id':id,'url':url,'version':arx,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Python-urllib/3'}),timeout=35) as r:b=r.read(8000000);a['final_url']=r.url
  assert b.startswith(b'%PDF')
  p=P/(str(id)+'.pdf');p.write_bytes(b);a.update(sha256=hashlib.sha256(b).hexdigest(),size=len(b));out.append(a)
  (P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
  subprocess.run(['pdftotext','-layout',str(p),str(P/(str(id)+'.txt'))],check=True)
  t=(P/(str(id)+'.txt')).read_bytes();a['derivative']={'path':str(id)+'.txt','sha256':hashlib.sha256(t).hexdigest(),'size':len(t)}
 except Exception as e:a['failure']=str(e);out.append(a) if a not in out else None
 (P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
