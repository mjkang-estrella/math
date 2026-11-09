import signal
signal.alarm(140)
import pathlib,json,urllib.request,hashlib,datetime,concurrent.futures,subprocess,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
L=pathlib.Path(__file__).resolve().parent
J=json.loads((L/'literal-records.json').read_text()); urls=sorted(set(v['record']['source_url'].split('/abs/')[1] for v in J.values()))
def get(a):
 out=[]
 for kind,url in [('abs','https://arxiv.org/abs/'+a),('pdf','https://arxiv.org/pdf/'+a)]:
  row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  try:
   with urllib.request.urlopen(url,timeout=18) as r:b=r.read();row['status']=r.status;row['final_url']=r.url
   p=L/(a+'.'+kind);p.write_bytes(b);row.update(sha256=hashlib.sha256(b).hexdigest(),path=p.name)
   if kind=='pdf':subprocess.run(['pdftotext','-layout',str(p),str(L/(a+'.txt'))],timeout=10,capture_output=True)
  except Exception as e:row['error']=str(e)
  out.append(row)
 return out
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for result in ex.map(get,urls):
  with (L/'source-receipts.jsonl').open('a') as f:
   for r in result:f.write(json.dumps(r)+'\n');print(r['url'],r.get('status',r.get('error')))
