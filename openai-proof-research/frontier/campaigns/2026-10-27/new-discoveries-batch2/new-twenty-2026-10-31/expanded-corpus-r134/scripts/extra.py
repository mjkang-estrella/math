import pathlib,json,urllib.request,hashlib,datetime,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
urls={'F-irregular-Schreib':'https://arxiv.org/pdf/2609.07745','F-irregular-Dovzhenok':'https://arxiv.org/pdf/2609.19245','modular-counterexamples':'https://arxiv.org/pdf/2608.10687','TWXI':'https://arxiv.org/pdf/2309.04390','flow-v1':'https://arxiv.org/pdf/2512.17342v1','nut-v1':'https://arxiv.org/pdf/2508.17842v1','prime-original':'https://www.renyi.hu/~gharcos/graphicness.pdf'}
r=[]
for name,url in urls.items():
 o={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=15) as f:b=f.read();o.update(status=f.status,sha256=hashlib.sha256(b).hexdigest())
  p=D/'sources'/f'{name}.pdf';p.write_bytes(b);subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 except Exception as e:o['error']=str(e)
 r.append(o);print(name,o,flush=True)
 (D/'sources/receipts-extra.json').write_text(json.dumps(r,indent=2)+'\n')
