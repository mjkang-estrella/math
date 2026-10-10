"""I152 evidence assembly only. No corpus traversal, inherited execution or sealing."""
from pathlib import Path
import json,hashlib,re
R=Path(__file__).resolve().parents[3]
S='frontier/sources/i152_algorithmic_sampling_reconstruction_discovery';E=S.replace('/sources/','/experiments/');OLD='frontier/sources/i148_polynomial_index_torus_subpackets';REPORT='frontier/iterations/i152-algorithmic-sampling-reconstruction-discovery.md'
def read(p):return (R/p).read_bytes()
def sha(b):return hashlib.sha256(b).hexdigest()
def data(p):return json.loads(read(p))
def write(p,x):(R/p).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
assert not (R/S/'seal.json').exists()
passages=[]
def add(p,a=1,b=None,credit='Actual complete displayed passage; combined ranges include explicitly recovered truncations.'):
 raw=read(p);ls=raw.decode().splitlines();b=b or len(ls);assert 1<=a<=b<=len(ls)
 passages.append(dict(local=p,file_sha256=sha(raw),start=a,end=b,line_count=len(ls),passage_sha256=sha('\n'.join(ls[a-1:b]).encode()),ending=ls[b-1],convention='splitlines; LF join without appended LF',credit=credit))
for p in [S+'/direct-context.txt',OLD+'/direct-context.txt','frontier/sources/i145_arithmetic_automorphic_discovery/direct-context.txt','frontier/sources/i142_uniform_algebraic_allocation/direct-context.txt','frontier/sources/i139_diffuse_weighted_positivity/direct-context.txt','frontier/sources/i136_birational_positivity_discovery/context-reading.txt']:
 add(p)
for x in data(S+'/input-freeze.json'):
 if x['path'] in ['AGENTS.md','sources/upstream.json']:add(x['snapshot'])
P='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/'
def source_dir(prefix):
 ds=list((R/P).glob(prefix+'*'));assert len(ds)==1;return str(ds[0].relative_to(R))
for prefix in ['Exact-Uniform-Sampling','An-FPRAS-for-Cell-Bounded','quantitative-lower-bounds-for-trace','Subpolynomial-query-complexity']:
 d=source_dir(prefix)
 for p in sorted((R/d/'build/sections').glob('*.tex')):add(str(p.relative_to(R)))
 add(d+'/build/main.tex')
for prefix,name in [('Exact-Uniform-Sampling','macros.tex'),('quantitative-lower-bounds-for-trace','preamble.tex'),('Subpolynomial-query-complexity','references.bib')]:add(source_dir(prefix)+'/build/'+name)
d=source_dir('Uniform-quasipolynomial')
for p in sorted((R/d/'build/manuscript').glob('*.tex')):add(str(p.relative_to(R)))
add(d+'/build/references/references.tex')
d=source_dir('A-latest-anchor')
for name in ['main.tex','summary.tex','part-1.tex']:add(d+'/build/'+name)
d=source_dir('Equidistribution-of-Prime-Degree-Torus')
for name in ['paper.tex','packets.tex','local.tex','analytic.tex','geometry.tex','entropy.tex','adelic.tex']:add(d+'/build/'+name)
d=source_dir('Unrestricted-pro-modularity-at-the-prime-two-October-6')
for name in ['family.tex','hecke.tex']:add(d+'/build/source/sections/'+name)
d=source_dir('Temperedness-at-ramified-places')
for name in ['introduction.tex','global.tex','local-criterion.tex']:
 p=d+'/build/sections/'+name
 if not (R/p).exists():
  choices=list((R/d/'build/sections').glob('*'+name.replace('local-criterion','local')+'*'));assert len(choices)==1;p=str(choices[0].relative_to(R))
 add(p)
# Additional original-audit source passages are taken from the exact earlier read record below,
# not silently expanded to whole manuscripts.
for prefix,suffix,a,b in [('The-Restricted-Geometric-Langlands','build/sections/01-introduction.tex',1,245),('Ramanujan-Arthur-Decompositions','build/sections/06-global.tex',1,568)]:
 ds=list((R/P).glob(prefix+'*'))
 if len(ds)==1 and (ds[0]/suffix).exists():add(str((ds[0]/suffix).relative_to(R)),a,b)
for p,a,b in [('frontier/sources/i148_polynomial_index_torus_subpackets/primary/khayutin-class.txt',1,749),('frontier/sources/i145_arithmetic_automorphic_discovery/primary/elmv09.txt',831,1185),('frontier/sources/i145_arithmetic_automorphic_discovery/primary/elmv09.txt',1196,1275),('frontier/sources/i145_arithmetic_automorphic_discovery/primary/elmv11-current.txt',2236,2590),('frontier/sources/i145_arithmetic_automorphic_discovery/primary/elmv11-current.txt',2781,2875),('frontier/sources/i148_polynomial_index_torus_subpackets/primary/wu.txt',1,180)]:add(p,a,b)
add('frontier/iterations/i77-weighted-switch-mixing.md')
for p,a,b in [('i29-common-base-entropy',1,48),('i126-random-geometry-discovery',177,187),('i128-statistical-learning-discovery',91,101),('i13-fresh-discovery',35,45),('i60-threshold-structural-combinatorics-discovery',7,17),('i72-graph-probability-discovery',264,274)]:add('frontier/iterations/'+p+'.md',a,b)
add(S+'/primary/hhp.txt')
for a,b in [(1,737),(953,1481),(1561,1702),(1899,1943)]:add(S+'/primary/stochastic.txt',a,b)
for a,b in [(88,245),(299,435),(975,1171)]:add(S+'/primary/picard.txt',a,b)
for a,b in [(1,125),(200,226),(2360,2396),(3530,3746)]:add('frontier/sources/i13_fresh_discovery/literature/chen-liu-2026.txt',a,b)
write(S+'/read-manifest.json',dict(passages=passages,scope='Only these actual read ranges are credited; other retained bytes and inherited receipts are not new semantic-reading claims.'))
inh=data(OLD+'/inheritance.json');refs={x['path']:x['sha256'] for x in inh['immutable']}
def ref(p):
 h=sha(read(p));assert p not in refs or refs[p]==h,(p,'immutable mismatch');refs[p]=h
oldseal=data(OLD+'/seal.json')
for p,h in oldseal['sha256'].items():
 assert sha(read(p))==h;ref(p)
ref(OLD+'/seal.json')
inh['anchors'].append(dict(base=OLD,seal=OLD+'/seal.json',sha256=sha(read(OLD+'/seal.json')),inventory=OLD+'/inventory.json'))
for p in [x['path'] for x in data(S+'/input-freeze.json') if x['path'] not in inh['live_ledgers']]+[x['local'] for x in passages if not x['local'].startswith(S+'/')]+[x['path'] for x in data(S+'/overlap-search.json')['refs']]:ref(p)
for p in ['frontier/sources/i13_fresh_discovery/literature/chen-liu-2026.pdf','frontier/sources/i29_common_base_entropy/literature/chen-liu-current.html']:ref(p)
assert not any(re.search(r'/(?:i|iteration)(150|151)[-_]',p) for p in refs)
inh['immutable']=[dict(path=p,sha256=h) for p,h in sorted(refs.items())]
inh['inherited_passages']+=data(OLD+'/read-manifest.json')['passages'];inh['lexical_records'].append(OLD+'/lexical-search.json')
inh['scope']='Flat immutable inheritance; no ancestor verifier/diagnostic execution and no active I150/I151 binding.'
write(S+'/inheritance.json',inh)
domain=data('frontier/sources/i112_inverse_boundary_discovery/search-domain.json');locals={x['local']:x for x in domain}
write(S+'/selected-source-bindings.json',[locals[p] for p in sorted({x['local'] for x in passages}&set(locals))])
retr=data(S+'/primary/retrieval.json')
for x in retr:
 if x.get('local','').endswith('.pdf') and x.get('extraction',{}).get('exit')==0:
  p=x['local'][:-4]+'.txt';x['text_path']=p;x['text_sha256']=sha(read(p));x['text_lines']=len(read(p).decode().splitlines())
write(S+'/primary/retrieval.json',retr)
write(S+'/reading-notes.json',dict(mandatory_context_completed_before_audit=True,original_audit_completed_before_discovery=True,checkpoint=S+'/original-audit-checkpoint.json',original_audit=S+'/original-audit-report.md',primary_versions={'hhp':'1708.02216v1, arXiv metadata August 7 2017; PDF internal date November 1 2021 retained literally','picard':'2609.06906v2 September 29 2026','stochastic':'PMLR336 1341–1372 2026, proceedings PDF','chen_liu':'2610.06724v1 October 5 2026; reused inherited PDF/text'},failed_or_truncated=['Original context truncations recovered: direct 80–96/95–125; inherited I148 92–110; inherited I145 510–530; earlier streams through their complete endings.','Broad original Arthur/dimension displays were truncated; only the actual selected recovered passages are credited.','First trace references path manuscript/references.bib failed; correct build/references/references.tex read completely.','First combined lower tools/block/coefficients display truncated; tools 130–158, block 1–90, coefficients 1–49 recovered.','First latest-anchor broad display truncated; 190–410 and 411–488 recovered.','Combined I77/I29 display truncated; all I77 recovered; I29 credited only 1–48.','Combined overlap JSON/evaluation display truncated in JSON; all 12 result lines and evaluation passage were displayed; paths/hashes are machine evidence only.','First combined Picard/Chen display truncated near Picard 407–1061; 407–419 and 975–1061 recovered separately.','Prevalidate.py inspection failed because filename is prevalidate-seal.py; correct source subsequently read, never executed.','Initial broad web-search results truncated; not proof evidence. Successful direct primary retrievals retained in primary/retrieval.json.'],normalization='Python str.splitlines; Unicode code-point spans from re.finditer; LF joining without terminal LF for passage hashes; byte SHA-256 and original Git blob SHA-1. Exact ordered lexical multisets.',scope='Read receipts, not formal or human certification. Unused context-normalization intermediates are mechanical decoding records, not extra reading claims.'))
# The inventory is assembled last and includes the future prevalidation receipt, but not its one seal.
owned={REPORT,E+'/validation.json'}
for base in [S,E]:
 for p in (R/base).rglob('*'):
  if p.is_file() and p.name!='seal.json':owned.add(str(p.relative_to(R)))
owned.add(S+'/inventory.json')
write(S+'/inventory.json',dict(owned_paths=sorted(owned),seal_path=S+'/seal.json',allowed_live_ledger_drift=inh['live_ledgers']))
print(json.dumps(dict(passages=len(passages),immutable=len(refs),owned=len(owned))))
