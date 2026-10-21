from pathlib import Path
import hashlib,json
ROOT=Path.cwd(); own=ROOT/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r121';out=own/'packet/private/incoming';out.mkdir(exist_ok=True)
paths=['AGENTS.md','sources/upstream.json',
'frontier/campaigns/2026-10-14/discovery-arithmetic-r120-parent/assessment.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r120/packet/READING.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r120/packet/notes/start.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r120/packet/notes/feasibility.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r120/packet/notes/saturated-fibre-reduction.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r59/original-scope.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r59/proof-attempts.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r60/candidate-proof.md']
rec=[]
for n,s in enumerate(paths):
 p=ROOT/s;b=p.read_bytes();q=out/(str(n).zfill(2)+'-'+p.name);q.write_bytes(b)
 rec.append({'incoming_original':s,'original_size':len(b),'original_sha256':hashlib.sha256(b).hexdigest(),'selection':'whole file','copy':str(q.relative_to(own)),'copy_size':len(b),'copy_sha256':hashlib.sha256(b).hexdigest()})
# The journal is never decoded in full. Whole-byte identity is late; retained selection is the actual initial overread.
p=ROOT/'frontier/NEW-TEN-2026-10-14.md';h=hashlib.sha256();size=0
with p.open('rb') as f:
 for b in iter(lambda:f.read(65536),b''):h.update(b);size+=len(b)
with p.open('rb') as f:b=b''.join(next(f,b'') for _ in range(100))
q=out/'10-journal-initial-1-100.md';q.write_bytes(b)
rec.append({'incoming_original':str(p.relative_to(ROOT)),'original_size':size,'original_sha256':h.hexdigest(),'selection':'lines1–100; original overread, late capture','copy':str(q.relative_to(own)),'copy_size':len(b),'copy_sha256':hashlib.sha256(b).hexdigest()})
p=ROOT/'sources/CONTENTS.md';b=p.read_bytes();lines=b.splitlines(keepends=True);selected=b''.join(lines[528:550]);q=out/'11-catalogue-529-550.md';q.write_bytes(selected)
rec.append({'incoming_original':str(p.relative_to(ROOT)),'original_size':len(b),'original_sha256':hashlib.sha256(b).hexdigest(),'selection':'lines529–550','copy':str(q.relative_to(own)),'copy_size':len(selected),'copy_sha256':hashlib.sha256(selected).hexdigest()})
(out.parent/'incoming-identities.json').write_text(json.dumps({'capture_timing':'after integrated derivation; not initial-byte attestation','records':rec},indent=2))
print('late captured',len(rec),'original identities and exact selections')
