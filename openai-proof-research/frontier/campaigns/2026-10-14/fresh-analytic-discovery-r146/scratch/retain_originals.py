from pathlib import Path
import hashlib,json
r=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r146')
paths=['AGENTS.md','sources/upstream.json',
'frontier/campaigns/2026-10-14/discovery-analytic-r145-parent/assessment.md']
paths += ['frontier/campaigns/2026-10-14/fresh-analytic-discovery-r145/'+x+'.md' for x in ['DERIVATION','GAPS','READING-LIMITS','ISOLATION','CHRONOLOGY']]
paths += ['frontier/iterations/i66-dispersive-equation-discovery.md','frontier/reviews/i68-logarithmic-blowup-novelty.md','frontier/reviews/i67-logarithmic-blowup-r2.md','frontier/campaigns/2026-10-14/fresh-analytic-discovery-r122/packet/public/nls-geometry.md','frontier/campaigns/2026-10-14/fresh-analytic-discovery-r122/packet/public/reading-limits.md']
a=[]
for i,name in enumerate(paths):
 b=Path(name).read_bytes(); rel=f'private/history/{i:02d}-{Path(name).name}'; dest=r/rel;dest.parent.mkdir(exist_ok=True,parents=True);dest.write_bytes(b)
 a.append(dict(original_path=name,selected_path=rel,size=len(b),sha256=hashlib.sha256(b).hexdigest()))
(r/'ORIGINALS-AUTH.json').write_text(json.dumps(dict(timing='Late byte identity capture after semantic reads and DERIVATION drafting; not assignment-time snapshots or inherited-seal validation.',entries=a),indent=2)+'\n')
print('retained exact selected bodies',len(a))
