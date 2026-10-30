"""Run only via the unchanged helper_guard.py with the prescribed environment."""
from pathlib import Path
import hashlib,json,datetime
P=Path(__file__).resolve().parent
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def run():
 rows=json.loads((P/'before.json').read_text())
 for r in rows:
  for key in ['path','copy']:
   p=Path(r[key]);assert p.stat().st_size==r['bytes'] and digest(p)==r['sha256'],str(p)
 for r in json.loads((P/'supplement-before.json').read_text()):
  for key in ['original','copy']:
   p=Path(r[key]);assert p.stat().st_size==r['bytes'] and digest(p)==r['sha256'],str(p)
 body=(P/'retrieved/changat-session-body.pdf').read_bytes()
 assert body.startswith(b'%PDF')
 assert hashlib.md5(body).hexdigest()=='895a973d1687ccf531f2e699e825c259'
 tree=json.loads((P/'retrieved/omega-blueprint-tree.json').read_text());assert not tree['truncated']
 blobs={r['path']:r['sha'] for r in tree['tree'] if r['type']=='blob'}
 paths=json.loads((P/'selected-registry-paths.json').read_text())
 for path in paths:
  b=(P/'retrieved/blueprints'/path.split('Graph/')[1].replace('/','__')).read_bytes()
  assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blobs[path]
 root=json.loads((P/'retrieved/omega-root.json').read_text())
 problem_sha=next(r['sha'] for r in root['tree'] if r['path']=='Problems')
 baseline=next((P/'copies/root-r165-preliminary-freeze-r1').rglob('omega-current-problems.json'))
 d=json.loads(baseline.read_text());assert problem_sha==d['sha'] and not d['truncated']
 assert len(d['tree'])==1567
 delta=json.loads((P/'retrieved/omega-fixed-delta.json').read_text())
 assert delta['total_commits']==22 and len(delta['files'])==11
 return {'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','original_and_copy_entries':len(rows),'supplement_entries':3,'repository_pdf_md5_matches':True,'current_blueprints_verified':len(paths),'blueprint_tree_entries':len(tree['tree']),'unchanged_Problems_entries':1567,'fixed_delta_commits':22,'fixed_delta_files':11,'worldwide_clearance':False,'credit':0}
if __name__=='__main__':print(json.dumps(run(),indent=2))
