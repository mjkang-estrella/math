import pathlib,json,hashlib,datetime,resource,concurrent.futures,urllib.request,urllib.error,subprocess,time
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
L=pathlib.Path(__file__).resolve().parent;S=L/'sources';S.mkdir(exist_ok=True);rows=json.loads((L/'literal-records.json').read_text());start=time.monotonic()
def fetch(a):
 if time.monotonic()-start>115:return
 name,url=a;p=S/name;rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research-source-review/1.0'}),timeout=9) as f:
   data=f.read(20000000);rec.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(data).hexdigest());p.write_bytes(data)
  if data[:4]==b'%PDF':subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],timeout=8,check=False)
 except Exception as e:rec.update(status=getattr(e,'code',None),error=str(e))
 p.with_name(p.name+'.receipt.json').write_text(json.dumps(rec,indent=2));print(name,rec.get('status'),flush=True)
items=[]
for a in sorted(set(x['record']['source_url'].split('/')[-1] for x in rows.values())):
 items.extend([(a+'.abs.html','https://arxiv.org/abs/'+a),(a+'.pdf','https://arxiv.org/pdf/'+a)])
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as e:list(e.map(fetch,items))
