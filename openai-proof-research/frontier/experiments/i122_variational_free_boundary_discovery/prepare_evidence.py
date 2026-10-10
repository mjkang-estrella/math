"""Development-only manifest preparation. Not imported or executed by verification. No seal creation."""
from pathlib import Path
import hashlib,json,re,runpy
ROOT=Path.cwd();S='frontier/sources/i122_variational_free_boundary_discovery';E='frontier/experiments/i122_variational_free_boundary_discovery'
def sha(b):return hashlib.sha256(b).hexdigest()
def obj(p):return json.loads(Path(p).read_bytes())
def save(p,o):Path(p).write_text(json.dumps(o,indent=2,ensure_ascii=False)+'\n')
def rec(p):b=Path(p).read_bytes();return {'path':p,'sha256':sha(b),'bytes':len(b)}
domain=obj('frontier/sources/i113_online_optimization_discovery/search-domain.json');bylocal={d['local']:d for d in domain}
P='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/'
rows=[]
def passage(p,start=1,end=None,purpose='',convention='LF'):
 b=Path(p).read_bytes();t=b.decode('utf8',errors='replace');ls=t.split('\n') if convention=='LF' else t.splitlines();end=end or len(ls)
 assert 1<=start<=end<=len(ls),(p,start,end,len(ls))
 d={'path':p,'sha256':sha(b),'start':start,'end':end,'total_lines':len(ls),'line_convention':convention,'passage_sha256':sha('\n'.join(ls[start-1:end]).encode()),'purpose':purpose}
 if p in bylocal:d['url']='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+bylocal[p]['path']
 rows.append(d)
for n in ['introduction','setup','algorithm','safety','transfer','accounting']:
 passage(P+'One-Sample-Suffices-for-Matroid-Prophet-Inequalities-against-an-Almighty-Adversary-September-23-2026/build/sections/'+n+'.tex',purpose='Complete original-I119 source operation audit, including section ending')
for n in ['introduction','geometry','reductions','blowup','interaction','completion']:
 passage(P+'Interior-regularity-of-planar-Mumford-Shah-minimizers-September-24-2026/build/sections/'+n+'.tex',purpose='Complete relevant planar hypotheses, reductions, compact-piece proof and completion through endings')
B=P+'The-critical-dimension-for-one-phase-Bernoulli-minimizers-September-24-2026/build/'
passage(B+'paper.tex',purpose='Exact minimizer class and accepted critical-dimension statement')
for n in ['history','reductions','consequences']:passage(B+'sections/'+n+'.tex',purpose='Complete relevant compactness/dimension-reduction/consequence operations; cone certificate not independently audited')
for p,a,b,purpose in [
 ('frontier/sources/i22_combinatorial_discovery/literature/strong-secretary.txt',730,916,'Complete ABHM refresh algorithm, invariant proof and complexity through ending'),
 ('frontier/sources/i22_combinatorial_discovery/literature/sample-ocrs.txt',90,270,'FSZ setup, spanning-chain construction and Theorem 2.5 proof through ending'),
 ('frontier/sources/i22_combinatorial_discovery/literature/sample-prophet.txt',1309,1366,'Fu Appendix C through ending; CRS scope'),
 ('frontier/sources/i113_online_optimization_discovery/external/dk19.txt',1120,1303,'DK19 Theorems 5.1/6.1 proofs through ending examples'),
 ('frontier/sources/i22_combinatorial_discovery/literature/iff-sfm.txt',278,612,'IFF implementation and strongly polynomial proof through Figure 3'),
 ('frontier/iterations/i22-combinatorial-discovery.md',70,118,'Exact cardinality-perturbed SFM interface'),
 ('sources/CONTENTS.md',8872,8929,'Actual catalogue entries for title leads'),
 (S+'/external/variable.txt',1,299,'Hypotheses and complete affine-change Lemma 2.1 proof; no complete Lipschitz proof reading claimed')]:passage(p,a,b,purpose)
for name in ['ee.txt','deangelis-v2.txt','sobral-v2.txt']:passage(S+'/external/'+name,purpose='Complete primary paper including all proof endings and bibliography; pdf layout LF convention')
for p,purpose in [
 ('AGENTS.md','Repository instructions'),
 ('frontier/iterations/i07-analysis.md','Independent constrained Ball-Evans overlap screen; entire report'),
 (S+'/original-i119-recursive-brief.txt','Entire required recursive original brief, reports, responses and objections'),
 ('frontier/iterations/i119-one-loss-online-selection.md','Entire original report audited before repairs'),
 ('frontier/experiments/i119-parent-verification.json','Finalized parent receipt and exact limitation of prior parent checks'),
 ('frontier/experiments/i119_one_loss_online_selection/verify.py','Complete inherited one-flat-replay interface')]:passage(p,purpose=purpose)
save(S+'/read-manifest.json',{'convention_note':'1-based inclusive lines. LF means text.split("\\n"); splitlines means Python splitlines. Passage joined with LF, no appended newline. Full-file final empty line is retained when present. PDF form feeds remain in LF lines. Ranges record actual reading, not selection-only inventory.','passages':rows})
contracts=[]
for d in rows:
 if d['path'] in bylocal:
  ls=Path(d['path']).read_text().split('\n')
  for i in range(d['start'],d['end']+1):
   for m in re.finditer(r'\\label\{(?:lem|thm|prop|cor|eq):[^}]+\}',ls[i-1]):contracts.append({'path':d['path'],'line':i,'needle':m.group(),'line_text':ls[i-1]})
save(S+'/source-contracts.json',contracts)
save(S+'/reading-references.json',[rec(p) for p in sorted({d['path'] for d in rows if not d['path'].startswith(S+'/')})])
# Flatten immutable owned inventories plus original receipts; no I120/I121 dependency.
paths=set()
for name,report in [('i113_online_optimization_discovery','frontier/iterations/i113-online-optimization-discovery.md'),('i116_robust_prophet_continuation','frontier/iterations/i116-robust-prophet-continuation.md'),('i119_one_loss_online_selection','frontier/iterations/i119-one-loss-online-selection.md')]:
 sp='frontier/sources/'+name+'/seal.json';paths.add(sp);paths.update(d['path'] for d in obj(sp)['files'])
paths.update('frontier/experiments/'+n+'-parent-verification.json' for n in ['i113','i116','i119'])
save(S+'/inherited-references.json',[rec(p) for p in sorted(paths)])
versions=[]
for d in obj(S+'/external-manifest.json'):
 if d.get('path','').endswith('-abs.html'):
  versions.append({'url':d['url'],'path':d['path'],'sha256':d['sha256'],'versions':re.findall(r'\[v[0-9]+\]',Path(d['path']).read_text())})
save(S+'/primary-versions.json',versions)
ledger=[];pattern=r'Mumford|Bernoulli|Ball.{0,8}Evans|I07|I119|eight|Eight|8/10'
for d in obj(S+'/inputs.json'):
 if d['may_drift']:
  for i,line in enumerate(Path(d['snapshot']).read_text().splitlines(),1):
   matches=list(re.finditer(pattern,line,re.I))
   if matches:ledger.append({'snapshot':d['snapshot'],'original':d['original'],'line':i,'text':line,'occurrences':[{'start':m.start(),'end':m.end(),'text':m.group()} for m in matches]})
save(S+'/ledger-overlap.json',{'expression':pattern,'flags':'IGNORECASE','line_convention':'splitlines','hits':ledger,'semantic_limit':'Status/overlap screen only, not full semantic review of unrelated ledger history.'})
save(S+'/literature-search.json',{'date':'2026-10-10','queries':['one phase free boundary quantitative stratification variable matrix coefficients','almost-minimizers quantitative stratification','Bernoulli Dini matrix packing','"Bernoulli" "Dini" "quantitative stratification"','"almost-minimizers" "variable coefficients" free boundary David Engelstein Toro regularity','"one-phase" "Dini" "Minkowski"'],'primary_proof_sources':[{'arxiv':'1702.04325v3','role':'Sharp quantitative stratification/packing source; complete proof read'},{'arxiv':'2609.26732v2','role':'Current planar proof; complete proof read'},{'arxiv':'1909.05043v2','role':'Hölder matrix almost-minimizer hypotheses; complete affine lemma read only'},{'arxiv':'2604.12712v2','role':'Dini Weiss formula; complete proof read; local bridge not new'}],'other_primary_leads_only':['https://arxiv.org/abs/1810.06963','https://arxiv.org/abs/1909.12597','https://arxiv.org/abs/2309.09283'],'limit':'A bounded current primary-literature screen, not proof of global priority or exhaustive absence. Search-engine relative publication ages are not used as version dates.'})
diag=runpy.run_path(E+'/diagnostics.py')['run']();save(E+'/diagnostics.json',diag)
with Path(S+'/validation-history.jsonl').open('a') as f:
 for row in [
 {'stage':'reading','status':'TRUNCATIONS_PRESERVED','details':'Several combined source/ledger reads exceeded output budget; relevant lost ranges were reread in bounded chunks. Later lexical metadata inspection also printed an oversized existing hits array; this did not stand in for proof reading.'},
 {'stage':'HTML_conversion','status':'FAIL','details':'ModuleNotFoundError: bs4. Successful original HTML retained; fallback selective Deangelis PDF/text retained. No failed attempt erased.'},
 {'stage':'PDF_extraction','status':'WARNING','details':'Deangelis pdftotext returned exit 0 with font-type mismatch warning; original PDF and extracted text both hash-bound.'},
 {'stage':'development_diagnostics','status':'PASS','checks':diag['checks'],'details':'First new exact-arithmetic execution passed. No original claim repaired.'}]:f.write(json.dumps(row)+'\n')
print(json.dumps({'read_passages':len(rows),'source_contract_memberships':len(contracts),'inherited_references':len(paths),'new_diagnostics':diag},indent=2))
