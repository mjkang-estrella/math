from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parents[1]
PROJECT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def sha(b):return hashlib.sha256(b).hexdigest()
b=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(b)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
t=json.loads(b);assert len(t['tree'])==13223 and not t['truncated'];tree={e['path']:e for e in t['tree']}
rows=[]
for fn in ('source-receipts.json','source169-receipts.json'):
 for r in json.loads((ROOT/'private'/fn).read_text()):
  p=ROOT/r['local'];d=p.read_bytes();e=tree[r['path']]
  blob=hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()
  assert e['size']==r['bytes']==len(d) and e['sha']==r['git_blob']==blob and sha(d)==r['sha256']
  assert r['url']==f'https://raw.githubusercontent.com/openai/math/{PIN}/{r["path"]}'
  rows.append(dict(r,canonical_tree_size=e['size'],canonical_tree_blob=e['sha'],authenticated=True))
paths=['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/NEW-TEN-2026-10-14.md']
base='frontier/campaigns/2026-10-14/'
paths += [base+'discovery-structural-r148-parent/assessment.md']
paths += [base+'fresh-structural-discovery-r148/notes/'+x for x in ('00-provenance-and-isolation.md','01-prefreeze-calculations.md','02-integrated-reduction-and-gap.md','03-evidence-and-reading-limits.md')]
paths += [base+'elementary-unimodality-r2/'+x for x in ('original-scope.md','candidate.md')]
paths += [base+'fresh-structural-discovery-r107/'+x for x in ('scope.md','proof-attempts.md','frame-obstruction.md')]
paths += [base+'fresh-structural-discovery-r54/original-scope.txt',base+'fresh-structural-discovery-r136/packet/public/derivations.md','frontier/iterations/i19-fresh-structural-discovery.md','frontier/iterations/i05-crossfield.md']
local=[]
for p in paths:
 d=(PROJECT/p).read_bytes();local.append({'path':p,'bytes':len(d),'sha256':sha(d)})
(ROOT/'private/incoming-authentication.json').write_text(json.dumps({'pin':PIN,'tree_sha256':sha(b),'pinned_source_files':rows,'late_local_original_snapshots':local,'limit':'Named incoming originals, not reduced-control membership, not whole-history or pre-observation change certificate.'},indent=2)+'\n')
print(json.dumps({'source_files_authenticated':len(rows),'late_named_original_snapshots':len(local)}))
