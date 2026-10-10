"""Authoring-only metadata preparation; never called by the offline verifier or seal replay."""
from pathlib import Path
import json,hashlib,re
S=Path('frontier/sources/i143_weighted_boundary_pole_control');E=Path('frontier/experiments/i143_weighted_boundary_pole_control');OLD=Path('frontier/sources/i140_nonlinear_elliptic_discovery')
assert not (S/'seal.json').exists(), 'sealed evidence cannot be changed'
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def binding(p):
 p=str(p);b=Path(p).read_bytes();return dict(path=p,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
reads=json.loads((S/'read-manifest.json').read_text())['passages']
exprs={'boundary':r'boundar(?:y|ies)|half[- ]?space|Dirichlet','coefficient':r'coefficients?|H[öo]lder|modulus','operation':r'virial|Pohozaev|pressure|interval|doubling|scaling|reflec\w*','verdict':r'PASS|FAIL|unresolved|PARK','exponent':r'alpha|beta|gamma|sigma|critical'}
found={k:[] for k in exprs};scope={}
for d in reads:scope.setdefault(d['path'],set()).update(range(d['start'],d['end']+1))
for p,ns in sorted(scope.items()):
 ls=Path(p).read_text().splitlines()
 for n in sorted(ns):
  for k,expr in exprs.items():
   for m in re.finditer(expr,ls[n-1],re.I):found[k].append(dict(path=p,line=n,start=m.start(),end=m.end(),match=m.group(),text=ls[n-1]))
dump(S/'focused-lexical.json',dict(expressions=exprs,occurrences=found,counts={k:len(v) for k,v in found.items()},scope='union of actually read lines, no duplicate counting for reread overlaps'))
flat={d['path']:d for d in json.loads((OLD/'immutable-flat.json').read_text())['files']}
se=json.loads((OLD/'seal.json').read_text())
for d in se['files']:flat[d['path']]=d
extra=[str(OLD/'seal.json'),'frontier/experiments/i140-parent-verification.json']
for d in json.loads((S/'context-manifest.json').read_text()):extra.extend(d[k] for k in ['path','snapshot','decoded'])
for d in json.loads((S/'originals.json').read_text()):extra.append(d['path'])
for d in json.loads((S/'snapshots.json').read_text()):
 if not d['drift']:extra.append(d['live'])
extra.extend(d['path'] for d in reads)
for p in extra:
 if p.startswith(str(S)+'/') or p.startswith(str(E)+'/'):continue
 b=binding(p)
 if p in flat:assert flat[p]['sha256']==b['sha256']
 flat[p]=b
assert not any(re.search(r'/(?:i|iteration)(141|142)',p) for p in flat)
dump(S/'immutable-flat.json',{'files':[flat[p] for p in sorted(flat)],'corpus_replay':'one flat pinned-domain traversal; no ancestor execution'})
dump(S/'selected-inventory.json',json.loads((OLD/'selected-inventory.json').read_text()))
verdicts={k:'PASS without repairs at original scope' for k in ['p-harmonic affine-lift obstruction','affine cubic normalization and modulus','affine completeness and dimension ten distinctions','C140 coupled doubling exponents','C140 coefficient and amplitude normalization','C140 low-exponent compactness positivity regularity','C140 annular and pole/scale bounds','C140 moving-pole Lr convergence origin continuity and strong minimum','C140 exact uniformity','O140a','O140b','O140c','V140 source mass potential harmonic constants','V140 distributional origin and inner boundary','V140 virial sign radial budget','V140 full short-interval endpoint error and layer identity','V140 localization pressure parameter order class uniformity','V140 marginal absorption dilation and contradiction','O140b finite-energy Pohozaev cancellation']}
dump(S/'original-audit-verdicts.json',{'original_I140':verdicts,'new_original_FAIL':[],'new_original_unresolved_paid_assertions':[],'unasserted_extensions':'remain distinct; no retrospective repairs','I125_original':'FAIL: canonical inventory','I125_ordering_only':'distinct PASS, not rerun','I122_original_general_Lambda':'FAIL preserved','I137_scope':'unchanged local development and R1-R7; no global label, interface, or arbitrary-near-minimizer screening'})
dump(S/'research-disposition.json',{'accepted_count':8,'remaining_count':2,'nomination':None,'qualitative_target_L':'technical bound via annular estimates and half-space cross Pohozaev','finite_scale_F143':'tracked in terms of K0; not effective evaluation of K0','parked':['effective numerical annular constant or independent effective exclusion','reflected radial Green pressure estimate','all previously parked branches'],'primary_versions':{'Li-Souplet':'arXiv 2408.17007v2, 5 June 2025','Dai-Peng':'version of record 6 December 2021; volume 13 article 12 (2022)','Phan':'1108.1312v1','Quittner-Souplet':'2407.04154v2, 26 September 2024','Bungert':'2302.08462v2, 10 October 2023'},'visual_reads':[{'path':str(S/'external/dai-peng-theorem.png'),'pdf_page':5},{'path':str(S/'external/li-souplet-theorem.png'),'pdf_page':2}]})
dump(S/'discovery-log.json',{'scope':'search discovery only, not proof reads','queries':['Henon Lane Emden halfspace Dirichlet bounded moving planes','Dai Qin halfspaces hyperbola','Liouville theorems for nonnegative solutions to Hardy Henon type system on a half space pdf','weighted halfspace 2025 2026'],'leads_used':['https://arxiv.org/abs/2408.17007','https://link.springer.com/article/10.1007/s43034-021-00158-1'],'other_leads_not_premises':['fractional and higher order scalar equations','mixed order exponential halfspace systems'],'retrievals':str(S/'external/retrievals.json'),'failures':'No failed new HTTP/PDF retrieval in final retrieval log; earlier subscription preview was not the full proof. Inherited failures remain in immutable ancestor evidence.','truncation':'Broad discovery listings and a combined original-context display truncated; context repair is recorded in context-reading.json. No truncated proof read is recorded as complete.'})
print(json.dumps({'flat_references':len(flat),'passages':len(reads),'lexical_occurrences':sum(map(len,found.values()))}))
