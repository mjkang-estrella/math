import os,json,gzip,hashlib,re,time,urllib.request,urllib.error
from pathlib import Path
L=Path(__file__).resolve().parent;R=L.parents[5];old=L.parent/'sol-fresh-source-discovery-r133'
pat=re.compile(rb'2404[.]10654|Hungarian.{0,8}roulette|s11634-026-00709|Barbiero|Frank.{0,90}(?:attenuat|discret|correl)|p53[.]pdf|Kendall.{0,100}surface|Fern.ndez.{0,30}Trutschnig',re.I)
cut=1793315389 # 2026-10-29 23:09:49 UTC
stats=dict(alias_paths=0,changed=[],missing=[],new_originals=[],hits=[],r111_r113_originals=[])
known=set()
with gzip.open(old/'history-aliases.jsonl.gz','rt') as f:
 for line in f:
  h,p=json.loads(line);known.add(p);stats['alias_paths']+=1;q=R/p
  if re.search(r'r11[123]/.*(?:SUMMARY|discovery|PROOF|review|DECISION)',p,re.I):stats['r111_r113_originals'].append(p)
  try:
   if q.stat().st_mtime<=cut:continue
   b=q.read_bytes();hh=hashlib.sha256(b).hexdigest()
   if hh==h:continue
   stats['changed'].append(dict(path=p,hash=hh))
   if pat.search(b):stats['hits'].append(p)
  except OSError:stats['missing'].append(p)
# Enumerate only to identify newly created original disposition records; no new inventory.
for root,ds,fs in os.walk(R/'frontier'):
 ds[:]=[d for d in ds if d not in {'.git','.lake','node_modules','__pycache__','.venv'} and Path(root)/d!=L]
 for n in fs:
  if n.lower() not in {'summary.md','discovery.md','proof.md','review.md','decision.md'}:continue
  q=Path(root)/n;p=str(q.relative_to(R))
  if p in known:continue
  b=q.read_bytes();stats['new_originals'].append(dict(path=p,sha256=hashlib.sha256(b).hexdigest()))
  if pat.search(b):stats['hits'].append(p)
(L/'freshness-receipt.json').write_text(json.dumps(stats,indent=2)+'\n')
print({k:len(v) if isinstance(v,list) else v for k,v in stats.items()})
# Fetch only actual changed proof/source bodies, not generated digestion echoes.
j=json.loads((L/'sources/omega-compare.json').read_text());head=json.loads((L/'sources/omega-head.json').read_text())['sha']
receipts=[]
for x in j['files']:
 p=x['filename']
 if not p.endswith(('.md','.lean')) or p.startswith(('Meta/','Golden/','Reg/')):continue
 url='https://raw.githubusercontent.com/the-omega-institute/trureturing/'+head+'/'+p;rec=dict(url=url,path=p,utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()))
 try:
  with urllib.request.urlopen(url,timeout=25) as r:b=r.read(6000001);rec['status']=r.status
  name='sources/delta-'+str(len(receipts))+Path(p).suffix;(L/name).write_bytes(b);rec.update(copy=name,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),match=bool(pat.search(b)))
 except Exception as e:rec['error']=str(e)
 receipts.append(rec)
(L/'registry-body-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n');print('delta bodies',len(receipts),[(r['path'],r.get('match'),r.get('error')) for r in receipts])
