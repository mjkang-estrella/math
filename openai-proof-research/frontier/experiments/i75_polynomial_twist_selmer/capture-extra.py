import pathlib,json,urllib.request,hashlib,datetime,subprocess
S=pathlib.Path('frontier/sources/i75_polynomial_twist_selmer');P=S/'primary';recs=[]
for name,url in [('tunnell','https://sites.math.rutgers.edu/~zeilberg/EM22/JT1983.pdf'),('dokchitser','https://arxiv.org/pdf/1208.5519v4')]:
 r={'name':name,'url':url,'started':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':str(P/(name+'.pdf'))}
 try:
  with urllib.request.urlopen(url,timeout=45) as f:data=f.read();r.update(status=f.status,final_url=f.url,headers=dict(f.headers.items()))
  pathlib.Path(r['path']).write_bytes(data);r.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
  z=subprocess.run(['pdftotext','-layout',r['path'],'-'],capture_output=True);(P/(name+'.txt')).write_bytes(z.stdout);r.update(extraction_exit=z.returncode,extraction_stderr=z.stderr.decode())
 except Exception as e:r['error']=repr(e)
 recs.append(r)
(S/'requests-extra.json').write_text(json.dumps(recs,indent=2)+'\n');print([{k:v for k,v in r.items() if k in ['name','status','error','bytes']} for r in recs])
