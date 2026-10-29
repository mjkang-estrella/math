import urllib.request,json,hashlib,datetime,pathlib,subprocess
p=pathlib.Path(__file__).parent
urls={'tossa12.pdf':'https://cs.uwaterloo.ca/journals/JIS/VOL28/Tossavainen/tossa12.pdf','aa55.pdf':'https://math.colgate.edu/~integers/aa55/aa55.pdf','subtraction.pdf':'https://zhangshenxing.github.io/publications/Zhang2024tcs%20On%20the%20linearity%20of%20the%20periods%20of%20subtraction%20games.pdf','omega-head.json':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD','openai-head.json':'https://api.github.com/repos/openai/math/commits/HEAD'}
r=[]
for name,url in urls.items():
 x={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=30) as f:b=f.read();x.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  (p/'sources'/name).write_bytes(b)
  if name.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(p/'sources'/name),str(p/'sources'/name.replace('.pdf','.txt'))],check=True)
 except Exception as e:x['error']=str(e)
 r.append(x)
(p/'http.json').write_text(json.dumps(r,indent=2))
