import urllib.request,hashlib,json,pathlib,datetime,subprocess
D=pathlib.Path(__file__).parent
out=[]
for name,ar in [('335749','1704.00851v1'),('335749-successor','1812.00321v1'),('336787','1708.01849v1'),('339244','1805.05207v1')]:
 url='https://arxiv.org/pdf/'+ar;e={'name':name,'url':url,'version':ar,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'headers':{'User-Agent':'Python-urllib/3'}}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers=e['headers']),timeout=40) as r:b=r.read(15000000);e['final_url']=r.url
  assert b.startswith(b'%PDF')
  p=D/(name+'.pdf');p.write_bytes(b);e.update(pdf_sha256=hashlib.sha256(b).hexdigest(),pdf_size=len(b));out.append(e)
  (D/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
  subprocess.run(['pdftotext','-layout',str(p),str(D/(name+'.txt'))],check=True)
  b=(D/(name+'.txt')).read_bytes();e.update(text_sha256=hashlib.sha256(b).hexdigest(),text_size=len(b))
 except Exception as err:e['failure']=str(err);out.append(e) if e not in out else None
 (D/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
