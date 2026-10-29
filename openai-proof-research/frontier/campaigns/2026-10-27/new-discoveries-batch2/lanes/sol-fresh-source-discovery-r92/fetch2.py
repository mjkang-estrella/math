exec((__import__('pathlib').Path(__file__).parent/'fetch.py').read_text().split('jobs=')[0])
jobs={'plactic-arxiv.pdf':'https://arxiv.org/pdf/2410.20460','properties.pdf':'https://arxiv.org/pdf/2512.21401','omega-delta.json':'https://api.github.com/repos/the-omega-institute/trureturing/compare/549177fd878744e25dce688cbf94dc2955e8958f...'+json.loads((L/'sources/omega-head.json').read_text())['sha']}
r=json.loads((L/'http.json').read_text())
for name,url in jobs.items():
 x={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'sources/'+name}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:b=f.read(16000000);x.update(status=f.status,final_url=f.url)
  p=L/'sources'/name;p.write_bytes(b);x.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  if b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 except Exception as e:x['error']=str(e)
 r.append(x)
(L/'http.json').write_text(json.dumps(r,indent=2));print(json.dumps(r[-3:],indent=2))
