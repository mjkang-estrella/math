from pathlib import Path
import json,re,hashlib,urllib.request,datetime,sys
P=Path(__file__).resolve().parent;R=next(x for x in P.parents if x.name=='openai-proof-research');B=P.parent.parent
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
def digest(f):
 h=hashlib.sha256()
 with f.open('rb') as s:
  for b in iter(lambda:s.read(65536),b''):h.update(b)
 return h.hexdigest()
def get(n,u):
 row={'name':n,'url':u,'utc':now()}
 try:
  with urllib.request.urlopen(u,timeout=25) as r:
   row['status']=r.status
   with (P/'sources'/n).open('wb') as f:
    while True:
     b=r.read(65536)
     if not b:break
     f.write(b)
  row.update(bytes=(P/'sources'/n).stat().st_size,sha256=digest(P/'sources'/n))
 except Exception as e:row['error']=str(e)
 rows=json.loads((P/'http.json').read_text()) if (P/'http.json').exists() else [];rows.append(row);(P/'http.json').write_text(json.dumps(rows,indent=2));print(json.dumps(row),flush=True)
if sys.argv[1]=='audit':
 pat=re.compile(r'Roggenkamp|Rumynin|semiperfect|2507[.]21316|2603[.]26626|Iwasawa|2608[.]22756|Chen.{0,20}Hussain|generalized moduli|generalised moduli',re.I)
 corpus=[];hits=[]
 for f in R.rglob('*'):
  if not f.is_file() or P in f.parents or f.suffix.lower() not in ('.md','.json','.txt') or not any(t in f.name.lower() for t in ['summary','discovery','findings','proof','review','ledger']):continue
  row={'path':str(f.relative_to(R)),'bytes':f.stat().st_size,'sha256':digest(f)};corpus.append(row)
  with f.open(errors='replace') as s:
   matched=[{'line':i,'text':l.strip()[:2400]} for i,l in enumerate(s,1) if pat.search(l)]
  if matched:hits.append({'path':row['path'],'hits':matched})
 (P/'duplicate-corpus.json').write_text(json.dumps(corpus,indent=2));(P/'duplicate-audit.json').write_text(json.dumps({'utc':now(),'pattern':pat.pattern,'files':len(corpus),'hits':hits,'limit':'All-date filename-selected streaming lexical screen, not semantic clearance'},indent=2));print(json.dumps(hits,indent=2)[:23000]);print('files',len(corpus))
 context=[]
 for f in [R/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'NEXT.md',B/'prior-campaign-context.json',R/'sources/upstream.json',R/'sources/CONTENTS.md']:
  obj=json.loads(f.read_text()) if f.suffix=='.json' else f.read_text();context.append({'path':str(f),'sha256':digest(f),'bytes':f.stat().st_size})
 (P/'context-read.json').write_text(json.dumps(context,indent=2))
 # checked literal regex, positive and negative controls
 assert pat.search('Roggenkamp 2507.21316 semiperfect');assert not pat.search('2507x21316')
elif sys.argv[1]=='fetch':
 for n,u in [('roggenkamp-abs.html','https://arxiv.org/abs/2507.21316'),('roggenkamp.html','https://arxiv.org/html/2507.21316v2'),('iwasawa-abs.html','https://arxiv.org/abs/2603.26626'),('iwasawa.html','https://arxiv.org/html/2603.26626v1'),('moduli-abs.html','https://arxiv.org/abs/2608.22756'),('moduli.html','https://arxiv.org/html/2608.22756v1'),('omega-head.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'),('openai-head.json','https://api.github.com/repos/openai/math/commits/HEAD')]:get(n,u)
elif sys.argv[1]=='closest':
 for n,u in [('woods.pdf','https://www.cambridge.org/core/services/aop-cambridge-core/content/view/DFDE3115600360262E19B4DFF7C972B8/S0008414X00048677a.pdf/some_results_on_semiperfect_group_rings.pdf'),('burgess.pdf','https://www.cambridge.org/core/services/aop-cambridge-core/content/view/S0008439500054151'),('roggenkamp-publisher.html','https://www.sciencedirect.com/science/article/abs/pii/S0021869325005484')]:get(n,u)
elif sys.argv[1]=='registry':
 out={'utc':now(),'live_head_refresh':'Both API head requests failed403 once; no retries or alternate head bypass','last_observed_omega':'73a5033dd654a16a14fcd1b13277f1a03d81d826','last_observed_omega_time':'2026-10-29T20:05:00Z via r104; commit19:55:36Z','last_observed_openai':'7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a','limits':'Complete18:13 path inventories plus inherited short chains are not semantic clearance. Old aggregate300-file cap remains. No current head attested here.'}
 pat=re.compile(r'Roggenkamp|Semiperfect|Iwasawa|YauAlgebra|GeneralizedModuli|GeneralisedModuli|ModuliAlgebra',re.I)
 for key in ['omega','openai']:
  f=P.parent/'root-edge-irregulator-final-freeze-r1'/f'{key}-tree.txt'
  with f.open() as s:matches=[l.rstrip().split('\t')[-1] for l in s if pat.search(l)]
  out[key]={'baseline_path':str(f),'sha256':digest(f),'pattern':pat.pattern,'matches':matches}
 (P/'registry.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2)[:10000])
