import pathlib,json,hashlib,re,datetime,urllib.request
O=pathlib.Path(__file__).resolve().parent; L=O.parent; G=L/'sol-renyi-registry-gap-closure-r3'
def sha(b):return hashlib.sha256(b).hexdigest()
pat=re.compile(r'Aivazidis|Loukaki|transversal|dissociat|subset.{0,25}product|factorial|pigeonhole|multiplicativ.{0,20}(independen|dependen)|12\.6|5\.6|阶乘|抽屉|鸽巢|子集.{0,12}[积乘]|t\^t|t!|Gamma.{0,10}t',re.I)
rows=[]; hits=[];missing=[]
intervals=json.loads((G/'intervals.json').read_text())
for it in intervals:
 p=pathlib.Path(it['response']);p=p if p.is_absolute() else G/p
 b=p.read_bytes();j=json.loads(b);fs=j['files'];r={'base':it['base'],'end':it['end'],'response':str(p),'sha256':sha(b),'expected_sha256':it['sha256'],'hash_match':sha(b)==it['sha256'],'files':len(fs),'commits':len(it['commits']),'patches':0,'missing':[]}
 for f in fs:
  text=f.get('patch','');r['patches']+=bool(text)
  if not text and f['status']!='removed':r['missing'].append(f['filename']);missing.append((it['end'],f['filename']))
  ms=list(pat.finditer(text))
  if ms:hits.append({'ref':it['end'],'path':f['filename'],'kind':'patch','excerpts':[text[max(0,m.start()-180):m.end()+280] for m in ms[:5]]})
 rows.append(r)
# Read original cached bodies, never the generated semantic-read/hit echoes.
bodies=[]
for x in json.loads((G/'bodies.json').read_text()):
 if x.get('status')!='ok':continue
 p=G/x['source'];b=p.read_bytes();t=b.decode(errors='replace')
 # Decode context JSON strings when the actual immutable body is JSON.
 try:
  j=json.loads(t)
  def strings(z):
   if isinstance(z,str):yield z
   elif isinstance(z,list):
    for v in z:yield from strings(v)
   elif isinstance(z,dict):
    for v in z.values():yield from strings(v)
  t+='\n'+'\n'.join(strings(j))
 except (ValueError,TypeError):pass
 ms=list(pat.finditer(t));bodies.append({'ref':x['ref'],'path':x['path'],'source':str(p),'url':x['url'],'sha256':sha(b),'bytes':len(b),'hits':len(ms),'reasons':x['reasons']})
 if ms:hits.append({'ref':x['ref'],'path':x['path'],'kind':'body','source':str(p),'excerpts':[t[max(0,m.start()-200):m.end()+350] for m in ms[:6]]})
delta=L/'sol-supertoken-preliminary-review-r1/omega-new-delta.json';b=delta.read_bytes();j=json.loads(b);new=[]
for f in j['files']:
 t=f.get('patch','');ms=list(pat.finditer(t));new.append({'path':f['filename'],'blob':f['sha'],'status':f['status'],'patch':bool(t),'hits':len(ms)})
 if ms:hits.append({'ref':'7f200dc4fad796eec490994c705245530200fd78','path':f['filename'],'kind':'later-patch','excerpts':[t[max(0,m.start()-180):m.end()+280] for m in ms[:5]]})
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'intervals':rows,'original_cached_bodies':bodies,'later_delta':{'path':str(delta),'sha256':sha(b),'commits':j.get('total_commits'),'files':new},'missing':missing}
(O/'registry-screen.json').write_text(json.dumps(out,indent=2));(O/'target-excerpts.json').write_text(json.dumps(hits,indent=2))
print('interval files',sum(x['files'] for x in rows),'patches',sum(x['patches'] for x in rows),'missing',len(missing),'bodies',len(bodies),'hits',len(hits),'later',len(new),'later missing',sum(not x['patch'] for x in new))
for x in hits:print(x['kind'],x['path'])
