import pathlib,json,hashlib,urllib.request,datetime,re,subprocess
P=pathlib.Path(__file__).resolve().parent;out=[]
for a in ['2311.01208','2310.06192','2401.14301','2402.14661']:
 u='https://arxiv.org/abs/'+a;e={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Python-urllib/3'}),timeout=20) as r:b=r.read(2000000)
  p=P/(a+'-abs.html');p.write_bytes(b);e.update({'path':p.name,'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
  out.append(e);(P/'successor-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
  versions=re.findall(re.escape(a)+r'v(\d+)',b.decode());v=max(map(int,versions)) if versions else None;e['latest_version_on_abs']=v
  if v and v>1:
   u='https://arxiv.org/pdf/'+a+'v'+str(v);e['pdf_url']=u
   with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Python-urllib/3'}),timeout=25) as r:b=r.read(12000000)
   assert b.startswith(b'%PDF');p=P/(a+'v'+str(v)+'.pdf');p.write_bytes(b);e.update({'pdf':p.name,'pdf_sha256':hashlib.sha256(b).hexdigest(),'pdf_size':len(b)})
   (P/'successor-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
   t=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True);b=t.read_bytes();e.update({'text':t.name,'text_sha256':hashlib.sha256(b).hexdigest(),'text_size':len(b)})
 except Exception as ex:
  e['failure']=str(ex)
  if e not in out:out.append(e)
 (P/'successor-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(a,e.get('latest_version_on_abs'),e.get('failure','ok'))
