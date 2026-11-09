import pathlib,json,hashlib,resource,os,datetime,urllib.request,subprocess
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3)); resource.setrlimit(resource.RLIMIT_CPU,(100,100)); os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
o=pathlib.Path(__file__).resolve().parent;b=o.parent.parent;d=json.loads((o/'inherited-selected.json').read_text()); sha=lambda x:hashlib.sha256(x).hexdigest()
r=json.loads((o/'reservation.json').read_text()); m=json.loads((b/'lanes/pi-mathdb-full-corpus-inventory-r301/manifest.json').read_text());print('manifest schema',str(m)[:300])
raw={}; refs=[]
for p in sorted((b/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 data=p.read_bytes(); h=sha(data); ent=next(e for e in m['files'] if e['path']=='corpus/'+p.name); assert h==ent['sha256'];print('verified',p.name,h)
 for n,line in enumerate(data.splitlines(keepends=True),1):
  obj=json.loads(line);i=str(obj.get('id',obj.get('mathdb_id')))
  if i not in d: continue
  (o/'raw').mkdir(exist_ok=True);(o/'raw'/f'{i}.jsonl').write_bytes(line);raw[i]=obj
  refs.append(dict(id=i,path=str(p),line=n,raw_sha256=sha(line),chunk_sha256=h,inherited_literal_sha256=d[i].get('literal_statement_sha256')))
assert len(raw)==40
(o/'raw-references.json').write_text(json.dumps(refs,indent=2));(o/'records.json').write_text(json.dumps(raw,indent=2));print('record schema',next(iter(raw.values())).keys())
(o/'sources').mkdir(exist_ok=True); receipts=[]
for name,url in [('registry-head','https://api.github.com/repos/OpenAI/math/commits/HEAD'),('365438','https://arxiv.org/pdf/2410.17057'),('382271','https://arxiv.org/pdf/2403.10665'),('360074','https://arxiv.org/pdf/2309.13783')]:
 rec=dict(name=name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'mathematical-research/1.0'}),timeout=35) as f:
   body=f.read();rec.update(status=f.status,final_url=f.url,headers=dict(f.headers),sha256=sha(body),bytes=len(body));p=o/'sources'/(name+('.pdf' if body.startswith(b'%PDF') else '.json'));p.write_bytes(body);rec['path']=str(p)
   if body.startswith(b'%PDF'): subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],timeout=20,check=True)
 except Exception as e:rec['error']=repr(e)
 receipts.append(rec);(o/'source-receipts.json').write_text(json.dumps(receipts,indent=2));print(name,rec.get('status'),rec.get('sha256'),rec.get('error'))
