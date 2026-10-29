from pathlib import Path
import json,re,hashlib,datetime,urllib.request
r=Path(__file__).resolve().parent;rows=[]
for lane in ['sol-fresh-source-discovery-r57','sol-polyomino57-full-final-review-r1']:
 for f in (r.parent/lane).rglob('*.json'):
  if not any(s in f.name for s in ['tree','D5','Problems','preprints']):continue
  try:d=json.loads(f.read_text())
  except:continue
  if not isinstance(d,dict) or 'tree' not in d:continue
  hits=[x['path'] for x in d['tree'] if re.search(r'binomial|Tarn|Tian|Coprim|ElementOrders',x['path'],re.I)]
  rows.append({'file':str(f),'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'tree_sha':d.get('sha'),'truncated':d.get('truncated'),'hits':hits})
(r/'registry-cached.json').write_text(json.dumps(rows,indent=2))
for x in rows:
 print(x['file'],len(x['hits']))
 for h in x['hits']:print(h)
url='https://raw.githubusercontent.com/the-omega-institute/trureturing/refs/heads/dev/README.md'
d={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.urlopen(url,timeout=25) as f:v=f.read();d['status']=f.status
 (r/'sources/omega-live-readme.md').write_bytes(v);d['sha256']=hashlib.sha256(v).hexdigest()
except Exception as e:d['error']=repr(e)
(r/'registry-live.json').write_text(json.dumps(d,indent=2))
