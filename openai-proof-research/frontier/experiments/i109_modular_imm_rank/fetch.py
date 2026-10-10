import pathlib,json,urllib.request,hashlib,subprocess
S=pathlib.Path('frontier/sources/i109_modular_imm_rank');(S/'external').mkdir(exist_ok=True)
urls={'chains.pdf':'https://arxiv.org/pdf/0709.3144v1','chains-metadata.html':'https://arxiv.org/abs/0709.3144','agkst-metadata.html':'https://arxiv.org/abs/2211.07691','abt-metadata.html':'https://eccc.weizmann.ac.il/report/2026/104/','forbes-metadata.html':'https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CCC.2024.31'}
records=[]
for name,url in urls.items():
 rec={'url':url,'name':name}
 try:
  with urllib.request.urlopen(url,timeout=45) as f: raw=f.read();rec['final_url']=f.url;rec['status']=f.status
  (S/'external'/name).write_bytes(raw);rec['sha256']=hashlib.sha256(raw).hexdigest()
  if name.endswith('.pdf'):
   out=S/'external'/name.replace('.pdf','.txt');r=subprocess.run(['pdftotext','-layout',str(S/'external'/name),str(out)],capture_output=True,text=True);rec.update(extraction_exit=r.returncode,extraction_stderr=r.stderr,text_sha256=hashlib.sha256(out.read_bytes()).hexdigest())
 except Exception as e:rec['failure']=repr(e)
 records.append(rec)
(S/'external-requests.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps(records,indent=2))
