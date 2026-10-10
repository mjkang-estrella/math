from pathlib import Path
import json,hashlib,re
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i80_geometric_flows_computation_discovery'
def sha(b):return hashlib.sha256(b).hexdigest()
def save(name,x):(S/name).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
m=json.loads((S/'source-manifest.json').read_text())
def source(k,suffix):return next(x for x in m if x['family']==k and x['path'].endswith(suffix))
deps=[]
for k,suffix,labels,use in [
 ('RV','build/addressed.tex',['thm:rapid','eq:rapid-capacity','eq:rapid-code','eq:rapid-transition','eq:rapid-transition-range','eq:rapid-scales','eq:rapid-total-memory','eq:rapid-small-motion','eq:rapid-divisibility','eq:rapid-history','eq:rapid-read','eq:rapid-velocity-estimate','eq:rapid-residual-estimate'],'C80 imports only finite configuration coding, all-address successor/terminal tables, effective scales/divisibility and order budgets; it replaces the velocity gate.'),
 ('RV','build/main.tex',['eq:energy-class','lem:realization','lem:projection'],'C80 uses the reference-pair uniqueness class; periodic projection is a scope exclusion, not its construction.'),
 ('FP','build/analytic-appendix.tex',['lem:realization','eq:energy-comparison'],'Underlying energy operation, including reference nonzero pressure and omission of competitor gradient bound.'),
 ('FS','build/main.tex',['thm:initialized','thm:shears'],'Contribution comparison: direct solenoidal forcing on a torus.'),
 ('GS','build/analytic-imports.tex',['sv:force'],'Contribution comparison: transverse pulses and zero self-advection on a torus.')]:
 e=source(k,suffix);s=(R/e['path']).read_text();positions=[]
 for lab in labels:
  needle='\\label{'+lab+'}';assert needle in s,(e['path'],lab)
  positions.append(dict(label=lab,line=s[:s.index(needle)].count('\n')+1))
 deps.append(dict(path=e['path'],git_blob=e['git_blob'],raw_url=e['raw_url'],sha256=e['sha256'],labels=positions,role=use))
save('dependencies.json',deps)
versions=[]
for p in sorted((S/'primary').glob('*-abs.html')):
 s=p.read_text();hit=re.search(r'<div class="submission-history">(.*?)</div>',s,re.S);assert hit,p
 lines=s.splitlines(keepends=True);a=s[:hit.start()].count('\n')+1;b=s[:hit.end()].count('\n')+1
 versions.append(dict(path=str(p.relative_to(R)),sha256=sha(p.read_bytes()),start=a,end=b,passage_sha256=sha(''.join(lines[a-1:b]).encode()),observed_versions=re.findall(r'\[v(\d+)\]',hit.group(0)),history_text=re.sub('<[^>]+>',' ',hit.group(0)).strip()))
versions.append(dict(path=str((S/'primary/dgmp-published.txt').relative_to(R)),sha256=sha((S/'primary/dgmp-published.txt').read_bytes()),description='Historical filename only. Actual UPC author manuscript says compiled April 15, 2026 and is watermarked DRAFT; not a verified publisher final. DOI/publisher web retrieval failed and is retained.'))
save('primary-versions.json',versions)
save('review-status.json',dict(proof='COMPLETE_AUTHOR_PROOF_RELATIVE_TO_STIPULATED_RV_NOT_INDEPENDENTLY_ACCEPTED',contribution='POTENTIAL_NONTRIVIAL_COMPACT_PRESSURE_COMPATIBILITY_NOT_ACCEPTED',full_companion_read='INCOMPLETE',nomination='HELD',accepted_count_increment=0,open_math=['equivariant deformation with fixed points and family choices','prescribed cap scale convergence with matched vanishing remainder','arbitrary-core infinite harmonic-moment completion'],new_proved_partials=['harmonic pressure criterion','exact radial swirl multipole identity','finite harmonic-moment completion','balanced compact rotation gate','small-angle exact translation with all fixed derivative budgets','C80 compiler relative to RV'],scope='All source statements and lower proof operations accepted as stipulated; only applicability and new deductions examined. No further agents or commits.'))
print('dependencies',len(deps),'primary version records',len(versions))
