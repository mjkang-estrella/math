from pathlib import Path
import hashlib,json
P=Path.cwd();R=P/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r115'; out=R/'packet/private/incoming';out.mkdir(exist_ok=True)
paths=['AGENTS.md','sources/upstream.json','frontier/campaigns/2026-10-14/discovery-arithmetic-r114-parent/assessment.md','frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r114/packet/notes/start.md','frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r114/packet/notes/symplectic-reduction.md','frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r114/packet/READING.md','frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r60/original-scope.md','frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r60/candidate-proof.md','frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r60/cyclic-collars.md','frontier/campaigns/2026-10-14/t019s59-contribution-r1/review.md']
rows=[]
for i,s in enumerate(paths):
 b=(P/s).read_bytes(); q=out/f'{i:02d}-{Path(s).name}';q.write_bytes(b);assert q.read_bytes()==(P/s).read_bytes()
 rows.append(dict(original=s,copy=str(q.relative_to(R)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),kind='whole-current-copy',read='whole body read earlier; hash first recorded late, not first-read stability'))
for s,start,end in [('frontier/NEW-TEN-2026-10-14.md',1,170),('sources/CONTENTS.md',527,551)]:
 b=(P/s).read_bytes(); q=out/('excerpt-'+Path(s).name);excerpt='\n'.join(b.decode().splitlines()[start-1:end])+'\n';q.write_text(excerpt)
 rows.append(dict(original=s,copy=str(q.relative_to(R)),original_observed_sha256=hashlib.sha256(b).hexdigest(),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),kind='excerpt',lines=[start,end],warning='mutable original; no present/future whole-file stability claim'))
t=(P/'sources/preprints-tree.json').read_bytes();j=json.loads(t);assert hashlib.sha256(t).hexdigest()=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';assert len(j['tree'])==13223 and not j['truncated']
meta={'separation':'Current incoming-original identities, not selected packet membership, not inherited-manifest verification. No supplied detached original seal was replayed. Original bytes were only read, never changed.','tree':dict(path='sources/preprints-tree.json',size=len(t),entries=len(j['tree']),truncated=False,sha256=hashlib.sha256(t).hexdigest()),'items':rows}
(R/'packet/incoming-identities.json').write_text(json.dumps(meta,indent=2)+'\n');print('copied',len(rows))
