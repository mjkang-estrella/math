import json,pathlib,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent
old=P.parent/'sol-fresh-source-discovery-r45'/'sources'
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'limit':'API stopped after 403 rate-limit on openai main. No subsequent API calls; current Omega delta unavailable. No whole-dev absence or novelty clearance.'}
for key,files in [('omega',['omega-D5.json','omega-Problems.json']),('omega-main',['omega-main-tree.json']),('openai',['openai-preprints.json']),('aim',['aim-tree.json']),('count',['count-tree.json'])]:
 fresh=P/'sources'/f'{key}-head.json';prior=json.loads((old/f'{key}-head.json').read_text())
 head=json.loads(fresh.read_text())['sha'] if fresh.exists() else None
 out[key]={'fresh_head':head,'cached_head':prior['sha'],'same_head':head==prior['sha'],'scopes':[]}
 for f in files:
  data=(old/f).read_bytes();d=json.loads(data);assert not d.get('truncated')
  paths=[x['path'] for x in d['tree']];matches=[p for p in paths if any(t in p.lower() for t in ['plucking','hedgehog','landry','mobius','moebius','ibarra','temperley','gramdet'])]
  out[key]['scopes'].append({'file':str((old/f).resolve()),'sha256':hashlib.sha256(data).hexdigest(),'entries':len(paths),'truncated':False,'matches':matches,'current':head==prior['sha']})
(P/'registry-screen.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:{'current':v.get('same_head'),'head':v.get('fresh_head')} for k,v in out.items() if isinstance(v,dict)},indent=2))
