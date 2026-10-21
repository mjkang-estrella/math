from pathlib import Path
import json,hashlib
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research');R=P/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r125'
(R/'private/incoming').mkdir(exist_ok=True)
full=['AGENTS.md','sources/upstream.json','frontier/campaigns/2026-10-14/discovery-arithmetic-r124-parent/assessment.md']+['frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r124/'+n for n in ['READING.md','notes/start.md','notes/feasibility.md','notes/integrated-norm-reduction.md']]
rec=[]
for i,name in enumerate(full):
 b=(P/name).read_bytes();dest=R/'private/incoming'/f'{i:02d}-{Path(name).name}';dest.write_bytes(b)
 rec.append(dict(original=name,kind='whole original, late capture',size=len(b),sha256=hashlib.sha256(b).hexdigest(),selected_copy=str(dest.relative_to(R)),selected_size=len(b),selected_sha256=hashlib.sha256(b).hexdigest()))
# No whole-journal decode, identity or hash: exact requested section only.
chosen=[];active=False
with (P/'frontier/NEW-TEN-2026-10-14.md').open('rb') as f:
 for b in f:
  if b.startswith(b'## Acceptance and publication'):active=True
  elif active and b.startswith(b'## '):break
  if active:chosen.append(b)
b=b''.join(chosen);dest=R/'private/incoming/acceptance-section.md';dest.write_bytes(b)
rec.append(dict(original='frontier/NEW-TEN-2026-10-14.md',kind='section selection only',selection='Acceptance and publication to before next level2 heading',selected_copy=str(dest.relative_to(R)),selected_size=len(b),selected_sha256=hashlib.sha256(b).hexdigest()))
selections=[('sources/CONTENTS.md',3427,3442,'catalogue142.md'),('frontier/iterations/i104-modular-representation-discovery.md',178,205,'i104-selected.md'),('frontier/iterations/i108-galois-tuple-divisibility.md',73,91,'i108-selected.md'),('frontier/iterations/i110-galois-moment-cancellation.md',190,215,'i110-selected.md')]
for name,a,z,out in selections:
 chosen=[]
 with (P/name).open('rb') as f:
  for i,b in enumerate(f,1):
   if a<=i<=z:chosen.append(b)
   if i>=z:break
 b=b''.join(chosen);dest=R/'private/incoming'/out;dest.write_bytes(b)
 rec.append(dict(original=name,kind='line selection only; not whole-original identity',lines=[a,z],selected_copy=str(dest.relative_to(R)),selected_size=len(b),selected_sha256=hashlib.sha256(b).hexdigest()))
t=(P/'sources/preprints-tree.json').read_bytes();j=json.loads(t)
(R/'private/incoming-identities.json').write_text(json.dumps({'chronology':'late capture after integrated derivation; identities apply to captured bytes, not a claim to certify earlier reads','full_and_selected':rec,'complete_tree':dict(original='sources/preprints-tree.json',size=len(t),entries=len(j['tree']),truncated=j['truncated'],sha256=hashlib.sha256(t).hexdigest()),'selection_rule':'Every copied file is its own selected member. No inherited r124 or corpus manifest.'},indent=2)+'\n')
# Descriptive metadata of acquired rendered pages, independent of PDF manifest.
images=[]
for p in sorted((R/'private/primary').glob('*.png')):
 b=p.read_bytes();images.append(dict(path=str(p.relative_to(R)),size=len(b),sha256=hashlib.sha256(b).hexdigest()))
(R/'private/primary/render-identities.json').write_text(json.dumps(images,indent=2)+'\n')
print('Captured',len(rec),'whole-original/selected objects and',len(images),'render identities.')
