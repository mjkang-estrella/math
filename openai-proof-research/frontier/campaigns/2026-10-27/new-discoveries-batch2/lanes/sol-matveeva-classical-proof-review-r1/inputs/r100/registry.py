from pathlib import Path
import json,re,urllib.request,hashlib,datetime
P=Path(__file__).resolve().parent;S=P/'sources';log=[];out={}
pat=re.compile(r'matveeva|precursive|p.recursive|bruner|noferini|smith.*power|power.*smith|integral.*recurs',re.I)
for key in ['omega','openai']:
 base=P.parent/'root-edge-irregulator-final-freeze-r1'/(key+'-tree.txt'); matches=[]
 for line in base.open():
  path=line.strip().split('\t')[-1]
  if pat.search(path):matches.append(path)
 out[key]={'head':json.loads((S/(key+'-head.json')).read_text())['sha'],'baseline':str(base),'baseline_sha256':hashlib.sha256(base.read_bytes()).hexdigest(),'matches':matches}
chain=['1b999d9fda71df7537b62327147496d64a6f66ef','2130bf544f7858fc3c142bb9623b7ba9464e22ba','d2b0ee6e958cf646530d3476088494e349570b46','c80e3a31a64948bb3c8b407f9881aaf5b96d63b6','dce0de1df2fe2e301a5f9d9664ba00eb50f617cd',out['omega']['head']]
for i,(a,b) in enumerate(zip(chain,chain[1:])):
 url='https://api.github.com/repos/the-omega-institute/trureturing/compare/'+a+'...'+b
 try:
  r=urllib.request.urlopen(url,timeout=25);raw=r.read();name='registry-delta-'+str(i)+'.json';(S/name).write_bytes(raw);d=json.loads(raw);fs=d.get('files',[]);out['delta'+str(i)]={'base':a,'head':b,'commits':d.get('total_commits'),'files':len(fs),'possibly_capped':len(fs)>=300,'matches':[f['filename'] for f in fs if pat.search(f['filename'])]};log.append({'url':url,'file':'sources/'+name,'sha256':hashlib.sha256(raw).hexdigest(),'status':r.status})
 except Exception as e:log.append({'url':url,'error':str(e)})
 print(i,out.get('delta'+str(i)),flush=True)
(P/'registry.json').write_text(json.dumps(out,indent=2));(P/'registry-http.json').write_text(json.dumps(log,indent=2))
