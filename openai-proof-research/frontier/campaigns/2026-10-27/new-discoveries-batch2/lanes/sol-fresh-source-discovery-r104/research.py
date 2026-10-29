from pathlib import Path
import json,re,hashlib,urllib.request,datetime,sys
P=Path(__file__).resolve().parent; R=next(x for x in P.parents if x.name=='openai-proof-research'); B=P.parent.parent
def sha(b):return hashlib.sha256(b).hexdigest()
def get(name,url):
 row={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=22) as r:b=r.read(18000000);row['status']=r.status
  (P/'sources'/name).write_bytes(b);row.update(bytes=len(b),sha256=sha(b));return b
 except Exception as e:row['error']=str(e)
 finally:
  log.append(row);(P/'http.json').write_text(json.dumps(log,indent=2))
log=json.loads((P/'http.json').read_text()) if (P/'http.json').exists() else []
if sys.argv[1]=='audit':
 terms=re.compile(r'evolution.?algebra|quandle|2610[.]22248|2609[.]09183|2601[.]07057|2609[.]25023|02251|Kaygorodov|Tocino|Viruel',re.I)
 files=[];hits=[]
 for f in R.rglob('*'):
  if not f.is_file() or P in f.parents:continue
  if not (any(t in f.name.lower() for t in ['summary','discovery','findings','proof','review','ledger']) and f.suffix.lower() in ['.md','.json','.txt']):continue
  b=f.read_bytes();files.append({'path':str(f.relative_to(R)),'sha256':sha(b),'bytes':len(b)})
  lines=[{'line':i,'text':s[:1800]} for i,s in enumerate(b.decode(errors='replace').splitlines(),1) if terms.search(s)]
  if lines:hits.append({'path':str(f.relative_to(R)),'hits':lines})
 (P/'duplicate-corpus.json').write_text(json.dumps(files,indent=2));(P/'duplicate-audit.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'terms':terms.pattern,'files':len(files),'hits':hits,'limit':'Lexical all-date filename-selected report audit only; nonhits do not establish semantic clearance.'},indent=2));print(json.dumps(hits,indent=2)[:22000])
 context=[]
 for f in [R/'AGENTS.md',B/'AGENTS.md',B/'NEXT.md',B/'ledger.json',B/'prior-campaign-context.json',R/'sources/upstream.json',P.parent/'root-edge-irregulator-final-freeze-r1/CURRENT-REGISTRIES.json']:
  b=f.read_bytes();context.append({'path':str(f),'sha256':sha(b),'bytes':len(b)})
 (P/'context-read.json').write_text(json.dumps(context,indent=2))
elif sys.argv[1]=='fetch':
 for n,u in [('survey.html','https://arxiv.org/html/2610.22248v1'),('survey-abs.html','https://arxiv.org/abs/2610.22248'),('quandle.html','https://arxiv.org/html/2609.09183v1'),('quandle-abs.html','https://arxiv.org/abs/2609.09183'),('quandle-old.html','https://arxiv.org/html/2601.07057v1'),('hu.html','https://arxiv.org/html/2609.25023v1'),('complete.html','https://link.springer.com/article/10.1007/s00013-026-02251-0'),('omega-head.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'),('openai-head.json','https://api.github.com/repos/openai/math/commits/HEAD')]:
  b=get(n,u);print(n,len(b) if b else None,flush=True)
