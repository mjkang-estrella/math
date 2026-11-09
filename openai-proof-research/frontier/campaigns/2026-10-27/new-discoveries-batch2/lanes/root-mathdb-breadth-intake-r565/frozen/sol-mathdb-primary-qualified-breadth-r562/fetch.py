import pathlib,json,hashlib,urllib.request,datetime,subprocess
P=pathlib.Path(__file__).parent;out=[]
for name,version in [('equitable','1612.00648v1'),('overpartition','1701.07915v1'),('juggling','1702.05808v1')]:
 url='https://arxiv.org/pdf/'+version;d={'url':url,'version':version,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=35) as f:b=f.read();d['final_url']=f.url
  assert b.startswith(b'%PDF');p=P/(name+'.pdf');p.write_bytes(b);d.update(size=len(b),sha256=hashlib.sha256(b).hexdigest(),path=str(p))
  out.append(d);(P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
  subprocess.run(['pdftotext','-layout',str(p),str(P/(name+'.txt'))],check=True)
  t=P/(name+'.txt');b=t.read_bytes();d['derivative']={'path':str(t),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
 except Exception as e:d['failure']=str(e);out.append(d) if d not in out else None
 (P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
 print(d)
