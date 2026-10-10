"""Pre-seal assembly only. Never invoked by verifier."""
from pathlib import Path
import json,hashlib,collections
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i86_compact_solenoidal_computation_novelty_r3';O=R/'frontier/sources/i80_geometric_flows_computation_discovery/primary'
def H(b):return hashlib.sha256(b).hexdigest()
def put(n,d):(S/n).write_text(json.dumps(d,indent=2)+'\n')
def get(n):return json.loads((S/n).read_text())
def ref(p):
 p=Path(p);b=(R/p).read_bytes();return dict(path=str(p),sha256=H(b),bytes=len(b))
# Actual semantic reading recorded after consumption, not inferred from hashes.
primary=[]
def read(p,ranges,note):
 p=Path(p);ls=(R/p).read_text().split('\n');ls=[v+'\n' for v in ls[:-1]]+([ls[-1]] if ls[-1] else [])
 ranges=[(a,min(b,len(ls))) for a,b in ranges]
 primary.append(dict(**ref(p),lines=len(ls),line_model='LF',ranges=[dict(start=a,end=b,passage_sha256=H(''.join(ls[a-1:b]).encode())) for a,b in ranges],note=note))
for name in ['gavrilov-v1','clv-v1','brandolese-meyer','okabe-brandolese','dgmp-latest','dgmp-published','beltrami-v3']:
 p=(O/(name+'.txt')).relative_to(R);read(p,[(1,len((R/p).read_text().splitlines()))], 'Full actual extracted proof body read; dgmp-published historical filename denotes April 15 2026 DRAFT, not publisher final.')
for name in ['towards-fluid','ept-current','fm-current']:
 p=(S/'primary'/(name+'.txt')).relative_to(R);read(p,[(1,len((R/p).read_text().splitlines()))],'Full extracted body read.')
for name,rr,note in [('baldi',[(1,1335),(1850,1925)],'Full decisive dynamical construction through Section 3; excludes lengthy later Taylor appendix, not used in reduction.'),('ept-publisher',[(1,420)],'Publisher version title and complete decisive Section 2; Section 3 density not separately reread (arXiv full body read).'),('fm-publisher',[(220,610)],'Publisher decisive rescaling, translated fields, derivative estimates and proof; full arXiv body read.')]:
 p=(S/'primary'/(name+'.txt')).relative_to(R)
 if not (R/p).exists():
  print('MISSING',p);continue
 read(p,rr,note)
put('primary-reads.json',primary)
versions=[]
for a,b in [('clv-v1','clv-current'),('gavrilov-v1','gavrilov-current'),('beltrami-v3','beltrami-current')]:
 p=(O/(a+'.txt')).relative_to(R);q=(S/'primary'/(b+'.txt')).relative_to(R)
 versions.append(dict(old=ref(p),current=ref(q),text_identical=(R/p).read_bytes()==(R/q).read_bytes(),meaning='Identity permits reuse of full semantic read; HTTP PDF byte identity not claimed.'))
put('version-comparisons.json',versions)
refs=get('immutable-refs.json');paths={x['path'] for x in refs}
for f in ['primary-responses.json','primary-supplement-responses.json','primary-routing-responses.json','primary-almost-responses.json']:
 for x in get(f):
  for p in [x.get('path'),x.get('conversion',{}).get('text')]:
   if p and not p.startswith(str(S.relative_to(R))) and p not in paths:refs.append(ref(p));paths.add(p)
for x in primary:
 if not x['path'].startswith(str(S.relative_to(R))) and x['path'] not in paths:refs.append(ref(x['path']));paths.add(x['path'])
put('immutable-refs.json',refs)
m=get('fluid-manifest.json');q=get('read-queue.json');rr=get('reads.json');cov=collections.defaultdict(set)
for x in rr:cov[x['sha256']].update(range(x['start'],x['end']+1))
coverage=[]
for x in q:
 n=len((R/x['path']).read_text().splitlines());missing=sorted(set(range(1,n+1))-cov[x['sha256']]);assert not missing
 coverage.append(dict(path=x['path'],sha256=x['sha256'],lines=n,missing=missing,aliases=[a['upstream_path'] for a in m if a['sha256']==x['sha256']]))
put('read-coverage.json',dict(scope='C80 fluid companions only; not I80 broad G/R assignment',status='COMPLETE_RELEVANT_PINNED_FLUID_TEX_BODIES',distinct_files=len(q),physical_files=len(m),distinct_lines=sum(x['lines'] for x in coverage),files=coverage))
d=get('search-domain.json');names={x['upstream_path'].split('/')[1] for x in m}
put('fluid-pdf-representatives.json',[x for x in d if x['path'].split('/')[1] in names and x['kind']=='outside_pdf'])
# Exact raw pinned inputs without copying their 619 MB archive.
req=[json.loads(l) for l in (R/'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside-requests.jsonl').read_text().splitlines()]
put('outside-raw-refs.json',[dict(path=x['path'],local=x['local'],sha256=x['sha256'],git_blob=x['sha'],bytes=x['bytes'],extraction=x.get('extraction')) for x in req])
# Every off-family matching passage was read; selected contexts bind ambiguous uses.
hits=get('off-family-matches.json');groups=collections.defaultdict(list)
for i,x in enumerate(hits):groups[x[0].split('/')[1]].append(i)
classifications=[]
for name,idx in groups.items():
 note='Lexical overlap outside fluid routing: incompressibility in topology, pressure in statistical/variational equations, harmonic moments in other systems, or generic Navier–Stokes citations. No compact Euler routing construction in matching passages; not a full semantic read of this unrelated manuscript.'
 if 'Charged-Reduction' in name:note='Linear compact symmetric-stress inverse for divergence/divergence-divergence with moment constraints. It does not prescribe a rank-one nonlinear stress v tensor v, stationary Euler, or marked-particle gate. Context bound in extra-reads.'
 if 'Gaussian' in name:note='Random field/distribution harmonic moments, not velocity pressure cancellation; context bound where ambiguous.'
 classifications.append(dict(manuscript=name,hit_indices=idx,decision='EXCLUDED_NOT_CONTENT_MATCHED_STRONGER_FLUID_COMPANION',reason=note))
put('off-family-classification.json',dict(total_passages=len(hits),read_ranges=[[0,120],[120,260],[260,len(hits)]],scope='All retained off-family matching passages consumed; ambiguous contexts inspected, no claim to read all excluded manuscripts.',groups=classifications))
put('status.json',dict(evidence='PENDING_FINAL_READ_ONLY_REPLAY',significance='TECHNICAL',original_proof='I85_PENDING_NOT_READ_OR_BOUND',conditional='Contribution verdict conditional on original C80 correctness; independent reduction not original proof PASS.',accepted_increment=0,nomination='PARENT_ONLY_ORIGINAL_I80_HELD_HISTORY_UNCHANGED',worldwide_priority='NOT_CERTIFIED',remaining=['Publisher final for DGMP unavailable (403); retained UPC April 2026 DRAFT and current arXiv, neither used in reduction.','Baldi later Taylor coefficients and BM referenced thesis general-K proof not used; decisive relevant primary proofs read.','No exhaustive worldwide priority claim; no unrelated G/R complete reading.']))
