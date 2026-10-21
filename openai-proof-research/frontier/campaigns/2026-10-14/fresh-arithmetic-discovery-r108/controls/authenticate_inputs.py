"""Read-only retained-input authentication and optional named current-original checks."""
import argparse,fnmatch,hashlib,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1]);p.add_argument('--project',type=Path)
a=p.parse_args();r=a.root.resolve()
def sha(b): return hashlib.sha256(b).hexdigest()
patterns=['*analytic*r138*','*structural*r144*','*analytic*r137*','t177c143-*','*structural*r143*','t373e135-*','*analytic*r135*','*analytic*r136*','k369r134-*','t088p133-*']
def safe(rel):
 q=Path(rel)
 assert not q.is_absolute() and '..' not in q.parts
 assert not any(fnmatch.fnmatch(c.lower(),t) for c in q.parts for t in patterns)
 return q
b=(r/'private/controls/preprints-tree.json').read_bytes()
assert sha(b)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
t=json.loads(b);assert t['truncated'] is False and len(t['tree'])==13223
entries={e['path']:e for e in t['tree']};n=0
for name in ['source-metadata.json','source-polynomial-metadata.json','source-jacobsthal-metadata.json']:
 for rec in json.loads((r/'private'/name).read_text()):
  rel=safe(rec['path']);data=(r/'private/sources'/rel).read_bytes();e=entries[str(rel)]
  blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
  assert len(data)==rec['bytes']==e['size']
  assert blob==rec['git_blob']==e['sha'] and sha(data)==rec['sha256']
  assert rec['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+str(rel)
  n+=1
primary=0
for rec in json.loads((r/'private/primary-metadata.json').read_text()):
 name=rec['name'];assert sha((r/'private/primary'/f'{name}.pdf').read_bytes())==rec['sha256']
 assert sha((r/'private/primary'/f'{name}.txt').read_bytes())==rec['text_sha256'];primary+=1
rec=json.loads((r/'private/walsh-metadata.json').read_text())
assert sha((r/'private/primary/walsh2014v2.pdf').read_bytes())==rec['sha256']
assert sha((r/'private/primary/walsh2014v2.txt').read_bytes())==rec['text_sha256'];primary+=1
current=[]
if a.project:
 project=a.project.resolve()
 for rel,snap in [('AGENTS.md','AGENTS.md'),('sources/upstream.json','upstream.json'),('sources/preprints-tree.json','preprints-tree.json')]:
  data=(project/safe(rel)).read_bytes();assert data==(r/'private/controls'/snap).read_bytes()
  current.append({'path':rel,'baseline':'early retained control','unchanged':True,'sha256':sha(data)})
 for name in ['current-originals.json','current-originals-supplement.json']:
  for rec in json.loads((r/'private'/name).read_text())['records']:
   if rec['status'].startswith('missing'): continue
   rel=safe(rec['path']);src=project/rel
   assert not any(q.is_symlink() for q in [src,*src.parents])
   data=src.read_bytes();assert sha(data)==rec['sha256']
   assert data==(r/safe(rec['snapshot'])).read_bytes()
   current.append({'path':str(rel),'baseline':'late current-original capture only','unchanged':True,'sha256':sha(data)})
print(json.dumps({'complete_tree_entries':len(t['tree']),'authenticated_source_files':n,'authenticated_primary_pdf_text_pairs':primary,'current_originals':current,'limits':'Read-only byte checks, not source truth audits or mathematical gates. Late comparisons cover only named originals since capture.'},indent=2))
