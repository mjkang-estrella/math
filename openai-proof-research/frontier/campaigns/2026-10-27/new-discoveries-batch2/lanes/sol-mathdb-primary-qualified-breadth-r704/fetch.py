import pathlib,urllib.request,hashlib,json,datetime,subprocess
P=pathlib.Path(__file__).resolve().parent;out=[]
for id,ar in [(340477,'1809.07360v1'),(343304,'1907.09451v1'),(343919,'1909.11726v1')]:
 url='https://arxiv.org/pdf/'+ar;e={'mathdb_id':id,'url':url,'version':ar,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Python-urllib/3'})
  with urllib.request.urlopen(req,timeout=35) as r:b=r.read();e['final_url']=r.url
  assert b.startswith(b'%PDF');p=P/(str(id)+'.pdf');p.write_bytes(b);e.update(sha256=hashlib.sha256(b).hexdigest(),size=len(b));out.append(e)
  (P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
  subprocess.run(['pdftotext','-layout',str(p),str(P/(str(id)+'.txt'))],check=True)
  t=P/(str(id)+'.txt');b=t.read_bytes();e['derivative']={'path':t.name,'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'method':'pdftotext -layout','visual_review':False}
 except Exception as ex:e['failure']=str(ex);out.append(e) if e not in out else None
 (P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
