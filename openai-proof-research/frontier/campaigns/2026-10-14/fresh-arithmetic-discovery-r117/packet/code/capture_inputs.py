from pathlib import Path
import hashlib,json
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r117');d=R/'packet/private/incoming';d.mkdir(exist_ok=True)
paths=['AGENTS.md','sources/upstream.json','frontier/campaigns/2026-10-14/discovery-arithmetic-r116-parent/assessment.md','frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r116/packet/notes/start.md','frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r116/packet/notes/quadratic-bsd-reduction.md','frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r116/packet/READING.md','findings/F003-rational-singularities-undecidable.md','frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r14/checkpoint.md','frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r63/scope.md','frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r63/proof-attempts.md','frontier/NEW-TEN-2026-10-14.md','sources/CONTENTS.md']
ids=[]
for i,p in enumerate(paths,1):
 b=Path(p).read_bytes();limit=180 if p=='frontier/NEW-TEN-2026-10-14.md' else 140 if p=='sources/CONTENTS.md' else None
 c=b if limit is None else b''.join(b.splitlines(keepends=True)[:limit]);dest=d/f'{i:02d}-{Path(p).name}';dest.write_bytes(c)
 ids.append({'original':p,'whole_size':len(b),'whole_sha256_at_capture':hashlib.sha256(b).hexdigest(),'selected_copy':str(dest.relative_to(R)),'selected_size':len(c),'selected_sha256':hashlib.sha256(c).hexdigest(),'selection':'whole' if limit is None else f'lines1–{limit}','chronology':'LATE after first read, before integrated note; no claim original-read identity.'})
(R/'packet/incoming-identities.json').write_text(json.dumps(ids,indent=2));print(len(ids),'captures; no inherited manifests')
