import pathlib,json,hashlib,urllib.request,datetime,subprocess
P=pathlib.Path(__file__).parent
rows=json.loads((P/'source-provenance.json').read_text())
for a in ['1806.02441v1','1008.4927v1']:
 u='https://arxiv.org/pdf/'+a;r={'url':u,'version':a,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'headers':'generic User-Agent: Python-urllib','coverage':'not yet read'}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Python-urllib'}),timeout=25) as f:b=f.read(12000000);r['final_url']=f.url
  assert b.startswith(b'%PDF');p=P/(a+'.pdf');p.write_bytes(b);r.update(pdf_path=p.name,pdf_sha256=hashlib.sha256(b).hexdigest(),pdf_size=len(b));rows.append(r)
  (P/'source-provenance.json').write_text(json.dumps(rows,indent=2)+'\n')
  t=P/(a+'.txt');z=subprocess.run(['pdftotext','-layout',str(p),str(t)],capture_output=True,text=True,timeout=30);r['extraction_returncode']=z.returncode;r['extraction_stderr']=z.stderr
  if z.returncode==0:
   b=t.read_bytes();r.update(text_path=t.name,text_sha256=hashlib.sha256(b).hexdigest(),text_size=len(b))
 except Exception as e:
  r['failure']=str(e)
  if r not in rows:rows.append(r)
 (P/'source-provenance.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows,indent=2))
