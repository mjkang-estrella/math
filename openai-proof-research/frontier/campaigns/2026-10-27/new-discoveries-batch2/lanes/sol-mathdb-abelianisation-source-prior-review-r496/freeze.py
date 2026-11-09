from pathlib import Path
import hashlib,json
L=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes'); out=L/'sol-mathdb-abelianisation-source-prior-review-r496'; root=L/'root-mathdb-three-candidate-intake-r493'; a=root/'frozen/claude-mathdb-primary-qualified-breadth-r480'
def bind(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
paths=[root/'manifest.json',root/'bindings.json',a/'manifest.json',a/'bindings.json',a/'retained-sources.json',a/'briefs/P2-339564-abelianisation-proof.md',a/'sources/arxiv/1806.06821.pdf',a/'sources/arxiv/1806.06821.txt',L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']
(out/'input-bindings.json').write_text(json.dumps([bind(p) for p in paths],indent=2)+'\n')
checks=[]
for r in [root,a]:
 m=json.loads((r/'manifest.json').read_text()); fs=m['files']; fs=fs.items() if isinstance(fs,dict) else [(x['path'],x) for x in fs]
 for rel,e in fs:
  p=r/rel; b=bind(p); assert b['sha256']==e['sha256'] and b['size']==e['size'],str(p)
 checks.append({'root':str(r),'files_validated':len(m['files'])})
# Direct original/copy equality for assigned source bodies and brief only.
for rel in ['briefs/P2-339564-abelianisation-proof.md','sources/arxiv/1806.06821.pdf','sources/arxiv/1806.06821.txt']:
 p=L/'claude-mathdb-primary-qualified-breadth-r480'/rel;q=a/rel
 assert p.read_bytes()==q.read_bytes(),rel
 checks.append({'original':bind(p),'copy':bind(q)})
(out/'intake-integrity.json').write_text(json.dumps({'status':'PASS','checks':checks,'upstream_verifiers_executed':False},indent=2)+'\n')
print('Frozen input bytes and validated manifests/direct assigned originals.')
