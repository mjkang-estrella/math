from pathlib import Path
import hashlib,json,datetime
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research');R=P/'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r141'
items=[('AGENTS.md',None),('sources/upstream.json',None),('sources/preprints-tree.json',None),('sources/CONTENTS.md',[(9041,9130)]),('frontier/campaigns/2026-10-14/discovery-analytic-r140-parent/assessment.md',None)]
items += [('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r140/'+f,None) for f in ['DERIVATION.md','GAPS.md','READING-LIMITS.md','ISOLATION.md']]
items += [('frontier/iterations/i80-geometric-flows-computation-discovery.md',[(1,261)]),('frontier/reviews/i85-compact-solenoidal-computation-r2.md',[(1,38)]),('frontier/reviews/i86-compact-solenoidal-computation-novelty-r3.md',[(1,155)]),('frontier/iterations/i20-pde-kinetic-discovery.md',[(227,249)])]
orig=[];copies=[]
for i,(name,ranges) in enumerate(items):
 p=P/name;b=p.read_bytes();row={'canonical_original_path':str(p),'size':len(b),'computed_git_blob':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest(),'sha256':hashlib.sha256(b).hexdigest(),'observation_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};orig.append(row)
 # Metadata-only full-tree bytes are authenticated, not claimed read as manuscript bodies.
 if ranges:
  lines=b.splitlines(keepends=True);selected=b''.join(b''.join(lines[a-1:z]) for a,z in ranges)
 else:selected=b
 d=R/'private/original-selections'/f'{i:02d}-{p.name}';d.parent.mkdir(exist_ok=True);d.write_bytes(selected)
 copies.append({'original_sha256':row['sha256'],'original_path':str(p),'selected_path':str(d.relative_to(R)),'selection':'whole-byte copy' if ranges is None else {'one_based_inclusive_lines':ranges},'size':len(selected),'sha256':hashlib.sha256(selected).hexdigest()})
(R/'original-authentication.json').write_text(json.dumps({'scope':'Current late original observations, not historical seals or semantic reading certificates. No git command used.','files':orig},indent=2)+'\n')
(R/'selected-copy-membership.json').write_text(json.dumps({'scope':'Only these selections. No original manifest is used to certify this reduced collection. Read extents are in READING-LIMITS.md and can differ from copied extents.','files':copies},indent=2)+'\n')
print('Bound',len(orig),'original observations and selections')
