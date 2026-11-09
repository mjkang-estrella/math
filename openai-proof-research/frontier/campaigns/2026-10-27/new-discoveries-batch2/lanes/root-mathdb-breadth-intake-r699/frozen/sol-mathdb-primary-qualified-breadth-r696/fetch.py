import pathlib,json,urllib.request,datetime,hashlib,subprocess
O=pathlib.Path(__file__).resolve().parent
out=[]
for id,a in [(325243,'1303.6651v1'),(323814,'1207.4841v1'),(320721,'1011.4658v1')]:
 if id==323814:continue # version must be taken from assigned record, not guessed
 u='https://arxiv.org/pdf/'+a; entry=dict(mathdb_id=id,url=u,version=a,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),headers={'User-Agent':'Python-urllib/3','Accept':'application/pdf'})
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers=entry['headers']),timeout=35) as r:b=r.read(12000000);entry['final_url']=r.url
  assert b.startswith(b'%PDF');p=O/(str(id)+'.pdf');p.write_bytes(b);entry.update(sha256=hashlib.sha256(b).hexdigest(),size=len(b));out.append(entry);(O/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
  subprocess.run(['pdftotext','-layout',str(p),str(O/(str(id)+'.txt'))],check=True)
  t=(O/(str(id)+'.txt')).read_bytes();entry['derivative']={'path':str(O/(str(id)+'.txt')),'sha256':hashlib.sha256(t).hexdigest(),'size':len(t)}
 except Exception as e:entry['failure']=str(e);out.append(entry) if entry not in out else None
 (O/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
