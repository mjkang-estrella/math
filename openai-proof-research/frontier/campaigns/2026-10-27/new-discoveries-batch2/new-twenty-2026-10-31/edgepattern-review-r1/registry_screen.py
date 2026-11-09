from pathlib import Path
import json,urllib.request,datetime,hashlib,re,resource,os
resource.setrlimit(resource.RLIMIT_CPU,(120,120));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
out=Path(__file__).resolve().parent/'live'
def get(name,url):
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathDB-independent-review/1.0'}),timeout=25) as f:
   data=f.read(20000000);r.update(status=f.status,sha256=hashlib.sha256(data).hexdigest());(out/(name+'.json')).write_bytes(data)
  return json.loads(data)
 except Exception as e:r['error']=str(e);return None
 finally:(out/(name+'.receipt.json')).write_text(json.dumps(r,indent=2))
head=json.loads((out/'omega-head.body').read_text())['sha']; repo='https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'
root=get('omega-root',repo+head);rows=[]
if root:
 for sub in ['D5','Problems']:
  sha=next(x['sha'] for x in root['tree'] if x['path']==sub)
  d=get('omega-'+sub,repo+sha+'?recursive=1')
  if d:
   hits=[x['path'] for x in d['tree'] if re.search(r'342414|pirot|sereni|edge.?pattern|fractional.?chrom|1904.?05618',x['path'],re.I)]
   rows.append(dict(head=head,subtree=sub,truncated=d.get('truncated'),entries=len(d['tree']),matches=hits))
# OpenAI head is unchanged: screen already bound complete immutable tree independently.
cached=out.parent.parent/'edgepattern-formal-r1/prior/openai-preprints-tree.json'
d=json.loads(cached.read_text());rows.append(dict(head=json.loads((out/'openai-head.body').read_text())['sha'],subtree='preprints',truncated=d.get('truncated'),entries=len(d['tree']),matches=[x['path'] for x in d['tree'] if re.search(r'342414|pirot|sereni|edge.?pattern|fractional.?chrom|1904.?05618',x['path'],re.I)],cached_immutable_tree_sha256=hashlib.sha256(cached.read_bytes()).hexdigest()))
(out/'registry-screen.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
