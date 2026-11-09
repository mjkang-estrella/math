import urllib.request,urllib.error,pathlib,hashlib,json,datetime,subprocess
L=pathlib.Path(__file__).resolve().parent
rows=[]
for id in ['1712.05859v1','1901.00053v2']:
 url='https://arxiv.org/pdf/'+id; p=L/(id+'.pdf');r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=35) as f:b=f.read();r.update(status=f.status,final_url=f.url)
  p.write_bytes(b);r.update(sha256=hashlib.sha256(b).hexdigest(),size=len(b)); (L/'source-bindings.json').write_text(json.dumps(rows+[r],indent=2)+'\n')
  if b.startswith(b'%PDF'):
   t=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True);b=t.read_bytes();r['derivative']={'path':str(t),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
 except Exception as e:r['failure']=str(e)
 rows.append(r);(L/'source-bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows))
