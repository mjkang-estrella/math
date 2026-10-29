from pathlib import Path
import json,re,urllib.request,hashlib,concurrent.futures
P=Path(__file__).resolve().parent;S=P/'sources';log=[]
def fetch(n,u):
 try:
  r=urllib.request.urlopen(u,timeout=25);b=r.read();(S/n).write_bytes(b);log.append(dict(file='sources/'+n,url=u,status=r.status,sha256=hashlib.sha256(b).hexdigest()));return b
 except Exception as e:log.append(dict(url=u,error=str(e)));return None
chain=['1b999d9fda71df7537b62327147496d64a6f66ef','2130bf544f7858fc3c142bb9623b7ba9464e22ba','d2b0ee6e958cf646530d3476088494e349570b46','c80e3a31a64948bb3c8b407f9881aaf5b96d63b6',json.loads((S/'omega_head.json').read_text())['sha']]
pat=re.compile(r'choi|kiem|GITQuot|Kazhdan|moduli.*(characteristic|logconcav)|(characteristic|logconcav).*moduli',re.I)
base=P.parent/'root-edge-irregulator-final-freeze-r1';out={};changed=[]
for key in ['omega','openai']:
 hits=[]
 with (base/(key+'-tree.txt')).open() as f:
  for l in f:
   path=l.rstrip().split('\t')[-1]
   if pat.search(path):hits.append(path)
 out[key]={'baseline_sha256':hashlib.sha256((base/(key+'-tree.txt')).read_bytes()).hexdigest(),'baseline_matches':hits,'head':json.loads((S/(key+'_head.json')).read_text())['sha']}
 print(key,'baseline hits',len(hits))
for i,(a,b) in enumerate(zip(chain,chain[1:])):
 if a==b:continue
 raw=fetch('delta-'+str(i)+'.json','https://api.github.com/repos/the-omega-institute/trureturing/compare/'+a+'...'+b)
 if raw:
  d=json.loads(raw);fs=d.get('files',[]);out['delta'+str(i)]={'base':a,'head':b,'commits':d.get('total_commits'),'files':len(fs),'possibly_capped':len(fs)>=300}
  changed.extend(x['filename'] for x in fs if pat.search(x['filename']))
print('changed topic hits',changed)
fetch('ikl_successor','https://arxiv.org/html/2510.01086');fetch('ikl_successor_abs','https://arxiv.org/abs/2510.01086')
out['changed_topic_hits']=changed;out['coverage']='Complete frozen baseline inventories plus separate compare segments; any >=300-file segment is potentially capped; lexical topic search only, not universal semantic clearance.'
(P/'registry.json').write_text(json.dumps(out,indent=2));(P/'registry-http.json').write_text(json.dumps(log,indent=2))
