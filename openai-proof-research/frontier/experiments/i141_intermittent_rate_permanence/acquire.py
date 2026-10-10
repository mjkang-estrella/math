import urllib.request,pathlib,json,hashlib,subprocess,datetime
assert not pathlib.Path('frontier/sources/i141_intermittent_rate_permanence/seal.json').exists()
S=pathlib.Path('frontier/sources/i141_intermittent_rate_permanence');(S/'external').mkdir(exist_ok=True)
items=[('ads-2011.pdf','https://sontaglab.org/FTPDIR/angeli_leenheer_sontag_siap_online2011.pdf'),('cnp-current.html','https://arxiv.org/abs/1010.3050'),('craciun-current.html','https://arxiv.org/abs/1501.02860'),('komatsu-2025.html','https://www.sciencedirect.com/science/article/pii/S0167691125001884')]
log=[]
for name,url in items:
 r={'url':url,'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=35) as q:b=q.read();r.update(status=q.status,final_url=q.url,headers=dict(q.headers))
  p=S/'external'/name;p.write_bytes(b);r.update(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  if name.endswith('.pdf'):
   t=p.with_suffix('.txt');v=subprocess.run(['pdftotext','-layout',str(p),str(t)],capture_output=True);r.update(extraction_exit=v.returncode,extraction_stderr=v.stderr.decode());z=t.read_bytes();r.update(text_path=str(t),text_sha256=hashlib.sha256(z).hexdigest(),text_bytes=len(z))
 except Exception as e:r.update(status='failed',error=repr(e))
 log.append(r);print(name,r['status'])
(S/'http-log.json').write_text(json.dumps(log,indent=2)+'\n')
