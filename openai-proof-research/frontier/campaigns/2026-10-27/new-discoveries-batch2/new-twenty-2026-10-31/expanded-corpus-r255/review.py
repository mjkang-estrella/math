import pathlib,json,re,subprocess,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
L=pathlib.Path(__file__).resolve().parent; jobs=[]
for p in L.glob('*-pdf.body'):
 subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
for p in L.glob('*-abs.body'):
 s=p.read_text(); versions=sorted(set(re.findall(r'/abs/(\d{4}\.\d+v\d+)',s)))
 print(p.stem,versions)
 for v in versions:jobs.append([v+'-pdf','https://arxiv.org/pdf/'+v])
for n,repo in [('openai','openai/math'),('omega','the-omega-institute/trureturing'),('pool','Vilin97/lean-pool')]:
 d=json.loads((L/(n+'-head.body')).read_text());sha=d['sha'];print(n,sha);jobs.append([n+'-tree','https://api.github.com/repos/'+repo+'/git/trees/'+sha+'?recursive=1'])
(L/'version-jobs.json').write_text(json.dumps(jobs))
h=json.loads((L/'history-bodies.json').read_text()); ids=json.loads((L/'reservation.json').read_text())['ids']
for path,s in h.items():
 d=json.loads(s)
 print('\nHISTORY',path)
 if isinstance(d,dict):
  for k,v in d.items():
   if any(str(i) in str(k) or str(i) in json.dumps(v) for i in ids):print(k,json.dumps(v,ensure_ascii=False))
