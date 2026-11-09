"""Read cached receipts and one primary public source; do not traverse GitHub APIs."""
from pathlib import Path
import json,hashlib,datetime,urllib.request
P=Path(__file__).resolve().parent; B=P.parent.parent
(P/'sources').mkdir(exist_ok=True)
def receipt(p):
 b=p.read_bytes();return {'file':str(p),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)}
r7=B/'lanes/sol-fresh-analysis-discovery-r7'
old=json.loads((r7/'provenance.json').read_text())
registry=[]
for r in old['retrievals']:
 n=r.get('file','')
 if n not in ['omega-head.json','omega-D5-tree.json','omega-Problems-tree.json','count-head.json','count-root.json','count-registry.json','openai-head.json','openai-preprints-tree.json']:continue
 p=r7/'sources'/n
 entry={**r,'reused':True,'actual':receipt(p)}
 j=json.loads(p.read_text())
 if 'tree' in j:
  assert j['truncated'] is False
  entry.update(truncated=False,entries=len(j['tree']),target_path_matches=[x['path'] for x in j['tree'] if any(t in x['path'].lower() for t in ['0910.1571','319089','friedman','free-magma','freemagma','tian'])])
 if n.endswith('head.json'):entry.update(commit=j['sha'],commit_date=j['commit']['committer']['date'])
 registry.append(entry)
(P/'registry-screen.json').write_text(json.dumps(registry,indent=2)+'\n')
url='https://arxiv.org/html/0910.1571v1'
r={'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.urlopen(url,timeout=30) as f:
  data=f.read(2000000);r['status']=f.status
 p=P/'sources/tian.html';p.write_bytes(data);r.update(receipt(p))
except Exception as e:r['error']=str(e)
(P/'retrievals.json').write_text(json.dumps([r],indent=2)+'\n')
print(json.dumps({'retrieval':r,'registry_coverage':[{'file':q['file'],'date':q['retrieved_utc'],'commit':q.get('commit'),'matches':q.get('target_path_matches')} for q in registry]},indent=2))
