from pathlib import Path
import json,hashlib,re,shutil
r=Path(__file__).resolve().parents[1];repo=r.parents[3];p=r/'packet';reg=json.loads((p/'private/acquisition.json').read_text())
keep={
'A-singular-normal-affine':{'01-introduction.tex':'Complete introduction read.','06-algebraization.tex':'Complete finite-determinacy, approximation, freeness descent and affine shrinking read.'},
'Integral-Donovan':{'01_introduction.tex':'Complete introduction read.','03_rigidity.tex':'Complete body read, integral orbit/HH1/gradings/marking.'},
'Bounded-klt':{'introduction.tex':'Complete introduction read.','reduction.tex':'Complete body read.'},
'Foulkes-Conjecture':{'introduction.tex':'Complete introduction read.','reduction.tex':'Complete body read, including all-a whole-power polarization.'},
'Quadratic-Stabilization':{'paper.tex':'Complete monolithic proof read.'},
'Prescribed-large-volume':{'01-introduction.tex':'Complete introduction in sequential/overlapping displays, final exact sector recovered.','02-tilt.tex':'Lines1–195, normalization/discriminants/tilt support. Remaining body not wholly read.','03-analysis.tex':'Main uniform heat, matrix spectral and negative surface cohomology passages read, initial combined display truncated; not a complete read.','04-apex.tex':'Lines1–205 and380–550 read, full restriction-image proof reread separately. Intervening residual construction not wholly reread.','06-ambient.tex':'Lines1–205,260–500,600–720 read; full product-sector and prescribed-charge transfer passages, partial other intervals.','07-heart.tex':'Lines1–130 read: surface-heart and section-phase proof; rest not fully read. Full heart conclusion is a stipulated source premise read in introduction.','refs.bib':'Bibliographic navigation only.'}}
ret=[]
for x in reg:
 name=Path(x['local']).name; extent=None
 for prefix,entries in keep.items():
  if '/'+prefix in x['local'] and name in entries:extent=entries[name]
 x['retained']=extent is not None
 f=p/x['local'];x['bytes']=x['canonical']['size']
 if extent:
  x['reading_extent']=extent;x['labels_navigation_only']=re.findall(r'\\label\{([^}]+)\}',f.read_text());ret.append(x)
 elif f.exists():f.unlink()
for f in sorted((p/'private/upstream').rglob('*'),key=lambda x:len(x.parts),reverse=True):
 if f.is_dir() and not any(f.iterdir()):f.rmdir()
(p/'private/acquisition.json').write_text(json.dumps(reg,indent=2)+'\n')
(p/'private/source-register.json').write_text(json.dumps(ret,indent=2)+'\n')
# Deliberately selected mathematical histories, not campaign snapshots.
history=[
('frontier/experiments/i198_geometry_representation/analytic-attempt.md','Full §3; initial other-screen text partly read.'),
('frontier/experiments/i202_foulkes_quotient/analytic-attempt.md','Substantive sections read in an initially combined display; opening truncated. No complete appendix/experiment audit.'),
('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r32/screen-203.md','Complete.'),
('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r75/packet/public/research.md','Complete displayed research body.'),
('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r78/packet/public/research.md','Lines1–65 complete; Foulkes later discussion substantially read, combined display truncated elsewhere.'),
('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r83/packet/public/research.md','Complete.'),
('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r5/checkpoint.md','Relevant differential-operator and relative-coordinate passages; not whole file.'),
('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r79/packet/public/research.md','Lines80–120, complete free-tangent Fedosov comparison and start/end adjacent sections; not full paper.')]
hr=[]
for origin,extent in history:
 f=repo/origin
 if not f.exists():print('HISTORY MISSING',origin);continue
 dest=p/'private/history'/Path(origin).parts[-4]/Path(origin).name
 # use unambiguous index to avoid colliding generic filenames
 dest=p/'private/history'/f'{len(hr)+1:02d}-{Path(origin).name}'
 shutil.copyfile(f,dest);hr.append(dict(origin=origin,local=str(dest.relative_to(p)),sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),bytes=dest.stat().st_size,reading_extent=extent))
(p/'private/history-register.json').write_text(json.dumps(hr,indent=2)+'\n')
# Context identities, without copying complete unrelated recent rounds.
paths=['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/NEW-TEN-2026-10-14.md']
paths += [str(f.relative_to(repo)) for f in sorted((repo/'frontier/findings').glob('R0*.md')) if 23<=int(f.name[1:4])<=40]
for name in ['fresh-arithmetic-discovery-r80','fresh-arithmetic-discovery-r86','fresh-arithmetic-discovery-r87','fresh-structural-discovery-r117','fresh-structural-discovery-r123','fresh-analytic-discovery-r122']:
 base=repo/'frontier/campaigns/2026-10-14'/name
 paths += [str(f.relative_to(repo)) for f in (base/'packet/public').glob('*.md') if f.name not in ['RIGHTS.md','REPRODUCE.md','reproduction.md']]
 paths += [str(f.relative_to(repo)) for f in [base/'REPORT.md',base/'HANDOFF.md'] if f.exists()]
for name in ['discovery-arithmetic-r86-parent','discovery-arithmetic-r87-parent','discovery-structural-r123-parent','discovery-analytic-r122-parent']:paths.append('frontier/campaigns/2026-10-14/'+name+'/intake.json')
cr=[]
for s in paths:
 f=repo/s;cr.append(dict(origin=s,sha256=hashlib.sha256(f.read_bytes()).hexdigest(),bytes=f.stat().st_size))
(p/'private/context-identities.json').write_text(json.dumps(cr,indent=2)+'\n')
print('sources retained',len(ret),'removed',len(reg)-len(ret),'histories',len(hr),'context identities',len(cr))
