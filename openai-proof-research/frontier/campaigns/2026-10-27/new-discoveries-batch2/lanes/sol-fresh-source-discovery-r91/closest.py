exec((__import__('pathlib').Path(__file__).parent/'fetch.py').read_text().split('r=[]')[0])
jobs={'qwalk.pdf':'https://arxiv.org/pdf/2309.01123v1','poullot-thesis.pdf':'https://perso.imj-prg.fr/germain-poullot/wp-content/uploads/sites/41/2023/10/Thesis_Germain_POULLOT_print_version-1-30.pdf'}
for n,repo,base in [('omega','the-omega-institute/trureturing','e9c949019b00eb22ab88e81d6ac6b1047925d95d'),('openai','openai/math','7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a')]:
 h=json.loads((L/'sources'/(n+'-head.json')).read_text())['sha'];print(n,h)
 if h!=base:jobs[n+'-delta.json']=f'https://api.github.com/repos/{repo}/compare/{base}...{h}'
r=json.loads((L/'http.json').read_text())
for name,url in jobs.items():
 x={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'sources/'+name}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:b=f.read(15000000);x.update(status=f.status,final_url=f.url)
  p=L/'sources'/name;p.write_bytes(b);x.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  if b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 except Exception as e:x['error']=str(e)
 r.append(x)
(L/'http.json').write_text(json.dumps(r,indent=2));print(json.dumps(r[-len(jobs):],indent=2))
