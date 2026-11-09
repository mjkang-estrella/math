import pathlib,json,hashlib,datetime,urllib.request,subprocess
P=pathlib.Path(__file__).parent
out=[]
for ident,arx in [(319684,'1003.3509v1'),(320415,'1009.4225v1'),(320327,'1008.4749v1')]:
 url='https://arxiv.org/pdf/'+arx;e={'mathdb_id':ident,'url':url,'version':arx,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Python-urllib/3','Accept':'application/pdf'}),timeout=30) as r:b=r.read(12000000);e['resolved_url']=r.url
  assert b.startswith(b'%PDF') and len(b)<12000000
  f=P/(str(ident)+'.pdf');f.write_bytes(b);e.update({'pdf_sha256':hashlib.sha256(b).hexdigest(),'pdf_size':len(b)})
  out.append(e);(P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
  t=P/(str(ident)+'.txt');subprocess.run(['pdftotext','-layout',str(f),str(t)],check=True)
  b=t.read_bytes();e.update({'text_sha256':hashlib.sha256(b).hexdigest(),'text_size':len(b),'extraction':'pdftotext -layout; PDF bound before extraction, derivative bound before reading; no visual claim'})
 except Exception as err:e['failure']=str(err);out.append(e) if e not in out else None
 (P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
 print(e)
