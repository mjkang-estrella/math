import pathlib,json,hashlib,urllib.request,urllib.error,subprocess,datetime
L=pathlib.Path(__file__).resolve().parent
terms={'sunflower':['sunflower','Alweiss'],'PFR':['Freiman','PFR'],'threshold':['Kahn','Kalai','Park–Pham'],'packing':['Viazovska','sphere packing']}
records=[];hits={k:[] for k in terms}
(L/'dedup-flat').mkdir(exist_ok=True)
for i,p in enumerate(sorted(L.parent.glob('*/SCOUTING.md'))):
 if p.parent==L:continue
 data=p.read_bytes();h=hashlib.sha256(data).hexdigest();q=L/'dedup-flat'/('%04d.md'%i);q.write_bytes(data)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h==hashlib.sha256(q.read_bytes()).hexdigest()
 records.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h))
 s=data.decode(errors='replace').lower()
 for k,aliases in terms.items():
  if any(t.lower() in s for t in aliases):hits[k].append(str(p))
(L/'dedup-bindings.json').write_text(json.dumps(records,indent=2)+'\n')
(L/'dedup.json').write_text(json.dumps(hits,indent=2)+'\n')
access=[]
(L/'sources').mkdir(exist_ok=True)
for name,ident in [('sunflower','1908.08483v1'),('PFR','2311.05762v1'),('threshold','2203.17222v1'),('packing','1603.04246v1')]:
 url='https://arxiv.org/pdf/'+ident;r=dict(family=name,url=url,time=datetime.datetime.now(datetime.timezone.utc).isoformat(),prior_hits=len(hits[name]))
 try:
  with urllib.request.urlopen(url,timeout=30) as f:data=f.read(12000000);r['status']=f.status
  if not data.startswith(b'%PDF'):raise ValueError('non-PDF/challenge; no retry')
  p=L/'sources'/(ident+'.pdf');p.write_bytes(data);r['pdf_sha256']=hashlib.sha256(data).hexdigest()
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
  r['text_sha256']=hashlib.sha256(p.with_suffix('.txt').read_bytes()).hexdigest()
 except Exception as e:r['failure']=repr(e)
 access.append(r)
 (L/'access.json').write_text(json.dumps(access,indent=2)+'\n')
print([(x['family'],x.get('status'),x.get('failure'),x['prior_hits']) for x in access])
