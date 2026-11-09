import pathlib,json,hashlib,urllib.request,datetime,subprocess
P=pathlib.Path(__file__).resolve().parent
out=[]
for mid,a in [(340088,'2201.07637v1'),(345174,'2608.14251v1')]:
 u='https://arxiv.org/pdf/'+a;e={'mathdb_id':mid,'url':u,'version':a,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Python-urllib/3','Accept':'application/pdf'}),timeout=35) as r:b=r.read(15000000);e['final_url']=r.url
  assert b.startswith(b'%PDF')
  p=P/(str(mid)+'-successor.pdf');p.write_bytes(b);e.update({'path':p.name,'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'status':'bytes_bound_before_extraction'});out.append(e)
  (P/'other-successor-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
  q=P/(str(mid)+'-successor.txt');subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True);bb=q.read_bytes();e['derivative']={'path':q.name,'size':len(bb),'sha256':hashlib.sha256(bb).hexdigest()}
 except Exception as ex:e['status']='STOP';e['error']=str(ex);out.append(e) if e not in out else None
 (P/'other-successor-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
