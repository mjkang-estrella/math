import pathlib,urllib.request,urllib.error,hashlib,json,datetime,subprocess
P=pathlib.Path(__file__).parent;out=[]
for name,aid in [('volume-source','2012.09901v1'),('volume-successor','2207.14253v3'),('pascal','2301.12481v1'),('tepper','2205.04237v1')]:
 url='https://arxiv.org/pdf/'+aid;now=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(url,timeout=35) as r:b=r.read();status=r.status;headers=dict(r.headers)
 except urllib.error.HTTPError as e:b=e.read();status=e.code;headers=dict(e.headers)
 except Exception as e:out.append({'url':url,'utc':now,'error':repr(e)});continue
 fn=name+('.pdf' if b.startswith(b'%PDF') else '.response');(P/fn).write_bytes(b)
 row={'url':url,'version':aid,'utc':now,'status':status,'headers':headers,'file':fn,'size':len(b),'sha256':hashlib.sha256(b).hexdigest()};out.append(row)
 (P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
 if status in [403,429] or not b.startswith(b'%PDF'):continue
 subprocess.run(['pdftotext','-layout',str(P/fn),str(P/(name+'.txt'))],check=True)
 t=(P/(name+'.txt')).read_bytes();row['derivative']={'file':name+'.txt','size':len(t),'sha256':hashlib.sha256(t).hexdigest()}
 (P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
