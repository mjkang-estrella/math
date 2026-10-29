from pathlib import Path
import urllib.request,datetime,hashlib,json,subprocess
P=Path(__file__).resolve().parent
log=json.loads(P.joinpath('http.json').read_text())
for n,u in [('zagreb-classical.pdf','https://match.pmf.kg.ac.rs/electronic_versions/Match66/n2/match66n2_627-645.pdf'),('small-genus.pdf','https://admjournal.luguniv.edu.ua/index.php/adm/article/download/2211/pdf'),('hansen-arxiv.html','https://arxiv.org/abs/2304.02230')]:
 row={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=25) as r:b=r.read(10000000);row.update(status=r.status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));P.joinpath('sources',n).write_bytes(b)
  if n.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(P/'sources'/n),str(P/'sources'/n.replace('.pdf','.txt'))])
 except Exception as e:row['error']=str(e)
 log.append(row)
P.joinpath('http.json').write_text(json.dumps(log,indent=2))
# context was read in earlier bounded output; now record complete JSON parse and substantive inventory
batch=P.parent.parent
out=[]
for n in ['ledger.json','prior-campaign-context.json']:
 p=batch/n;b=p.read_bytes();j=json.loads(b);out.append({'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'keys':list(j)})
 def walk(x):
  if isinstance(x,dict):
   selected={k:v for k,v in x.items()if k in ['id','title','mathdb_id','proposed_result','reason','status','source_target']}
   if selected:print(json.dumps(selected,ensure_ascii=False))
   for v in x.values():walk(v)
  elif isinstance(x,list):
   for y in x:walk(y)
 walk(j)
P.joinpath('context-read.json').write_text(json.dumps(out,indent=2))
