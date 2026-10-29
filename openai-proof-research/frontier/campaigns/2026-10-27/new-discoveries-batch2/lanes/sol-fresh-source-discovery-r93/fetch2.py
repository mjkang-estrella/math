exec(open(__file__.replace('fetch2.py','fetch.py')).read().split('urls=')[0])
urls={'separable.pdf':'https://arxiv.org/pdf/2608.27583','hrs.pdf':'https://arxiv.org/pdf/1506.04174','separable-abs.html':'https://arxiv.org/abs/2608.27583'}
a=json.loads((P/'http.json').read_text())
for name,url in urls.items():
 r={'url':url,'file':'sources/'+name,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=35) as f:b=f.read(12000000);r.update(status=f.status,final_url=f.url)
  (S/name).write_bytes(b);r.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  if b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(S/name),str(S/name.replace('.pdf','.txt'))],check=True)
 except Exception as e:r['error']=str(e)
 a.append(r)
(P/'http.json').write_text(json.dumps(a,indent=2)+'\n')
print([(r['file'],r.get('status'),r.get('error')) for r in a])
