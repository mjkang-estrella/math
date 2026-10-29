import json,hashlib,pathlib,datetime
p=pathlib.Path('.').resolve();base=p.parent/'sol-fresh-source-discovery-r49';old=json.loads((base/'registry-screen.json').read_text());out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'registries':{},'limit':'Named complete cached scopes only. No whole-dev or semantic absence claim.'}
for k,r in old['registries'].items():
 h=json.loads((p/'sources'/(k+'-head.json')).read_text())['sha'];assert h==r['head'];sc=[]
 for scope in r['scopes']:
  f=base/scope['file'];b=f.read_bytes();assert hashlib.sha256(b).hexdigest()==scope['sha256'];data=json.loads(b);paths=[x['path'] for x in data['tree']];hits=[x for x in paths if any(w in x.lower() for w in ['pluck','hedgehog','landry','2311.18059','antiunimod'])];sc.append(dict(source=str(f),sha256=scope['sha256'],entries=len(paths),truncated=data.get('truncated'),hits=hits))
 out['registries'][k]=dict(head=h,head_unchanged_from_r49=True,scopes=sc)
(p/'registry-screen.json').write_text(json.dumps(out,indent=2));print({k:[s['hits'] for s in r['scopes']] for k,r in out['registries'].items()})
