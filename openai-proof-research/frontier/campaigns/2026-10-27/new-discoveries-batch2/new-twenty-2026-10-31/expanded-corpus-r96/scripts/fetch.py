import pathlib,json,urllib.request,hashlib,datetime,concurrent.futures,sys,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
L=pathlib.Path(__file__).resolve().parents[1]
rows=json.loads((L/'extracted.json').read_text()); jobs=[]
if 'registry' in sys.argv:
 jobs=[(f'registry-{repo.split("/")[-1]}',f'https://api.github.com/repos/{repo}/commits/HEAD') for repo in ['openai/math','the-omega-institute/trureturing']]
else:
 jobs=[(k,'https://arxiv.org/html/'+v['row']['source_url'].split('/')[-1]) for k,v in rows.items()]
def run(j):
 k,url=j; rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-review'}),timeout=12) as r:
   b=r.read(); rec.update(status=r.status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(L/f'sources/{k}.html').write_bytes(b)
 except Exception as e:rec['error']=str(e)
 (L/f'sources/{k}-receipt.json').write_text(json.dumps(rec,indent=2)); return k,rec
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for k,r in ex.map(run,jobs): print(k,r,flush=True)
