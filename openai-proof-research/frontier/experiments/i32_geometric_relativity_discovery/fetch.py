import pathlib,json,datetime,hashlib,concurrent.futures,urllib.request,urllib.error,subprocess,sys
R=pathlib.Path(__file__).resolve().parents[3];O=R/'frontier/sources/i32_geometric_relativity_discovery/literature';O.mkdir(parents=True,exist_ok=True)
ids=sys.argv[1:] or ['2609.05167v1','2409.18838v2','1109.2165v2','2402.10299v2','2610.07577v1','2411.04908v2']
def one(item):
 id,kind=item;url=f'https://arxiv.org/{kind}/{id}';name=id+('.pdf' if kind=='pdf' else '.html');p=O/name
 rec={'url':url,'path':str(p.relative_to(R)),'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research I32 provenance/1.0'}),timeout=45) as f:b=f.read();rec.update(status=f.status,final_url=f.url,headers=dict(f.headers))
 except urllib.error.HTTPError as e:b=e.read();rec.update(status=e.code,error=str(e))
 except Exception as e:b=str(e).encode();rec.update(status=None,error=str(e))
 p.write_bytes(b);rec.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
 if kind=='pdf' and b.startswith(b'%PDF'):
  q=p.with_suffix('.txt');r=subprocess.run(['pdftotext','-layout',str(p),str(q)],capture_output=True,text=True);rec.update(extraction_status=r.returncode)
  if q.exists():rec.update(text_path=str(q.relative_to(R)),text_sha256=hashlib.sha256(q.read_bytes()).hexdigest())
 return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as e:records=list(e.map(one,[(i,k) for i in ids for k in ['abs','pdf']]))
old=json.loads((O/'manifest.json').read_text()) if (O/'manifest.json').exists() else []
old=[r for r in old if r['url'] not in {s['url'] for s in records}]
(O/'manifest.json').write_text(json.dumps(old+records,indent=2)+'\n')
for r in records:print(r['url'],r['status'],r['bytes'])
