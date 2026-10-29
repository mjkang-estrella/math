exec(open(__file__.replace('prior.py','fetch.py')).read().split('jobs=')[0])
out=[]
def fetch(name,url):
 r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:b=f.read(8_000_000);r['status']=f.status
  p=P/'sources'/name;p.write_bytes(b);r.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  if name.endswith('.pdf') and b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
  return b
 except Exception as e:r['error']=str(e)
 finally:out.append(r)
head=json.loads((P/'sources/omega-head.json').read_text())['sha']
fetch('omega-compare.json',f'https://api.github.com/repos/the-omega-institute/trureturing/compare/6f8ee6614e0faf9dfa2cce46d1eb758dea97c335...{head}')
for name,path in [('collatz-body.md','Blueprint/D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.md'),('collatz-length.lean','D5/S1/Recurrence/GallardoRahavandrainyCollatzLengthBound.lean')]:fetch(name,f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{head}/{path}')
fetch('bajnok-vor.pdf','https://msp.org/cnt/2025/14-1/cnt-v14-n1-p01-p.pdf')
(P/'prior-http.json').write_text(json.dumps(out,indent=2))
print('omega',head)
