"""Preparation only. Does not seal; final sealing is a separate one-time step."""
from pathlib import Path
import sys,json,hashlib,re,io,contextlib
sys.dont_write_bytecode=True
ROOT=Path.cwd();S=Path('frontier/sources/i124_fractal_incidence_discovery');E=Path('frontier/experiments/i124_fractal_incidence_discovery')
assert not (S/'seal.json').exists()
H=lambda b:hashlib.sha256(b).hexdigest()
def dump(p,d):p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
t=(S/'supplied-task.txt').read_text()
markers=['--- ORIGINAL DIRECT I121 BRIEF ---','--- FULL RECURSIVE ORIGINAL RECORD: REQUIRED READ ---','--- ORIGINAL I121 REPORT ---','--- FINALIZED PARENT RESPONSE ---']
names=['supplied-direct-i121-brief.txt','supplied-recursive-record-instruction.txt','supplied-original-i121-report.txt','supplied-finalized-i121-parent-response.txt']
for i,n in enumerate(names):
 part=t.split(markers[i],1)[1]
 if i+1<len(names):part=part.split(markers[i+1],1)[0]
 (S/n).write_text(part)
dump(S/'input-freeze.json',dict(task=str(S/'supplied-task.txt'),markers=markers,parts=names,task_snapshot=str(S/'snapshots/frontier/iterations/iteration124-fractal-incidence-discovery-task.json'),recursive_task_snapshot=str(S/'snapshots/frontier/iterations/iteration121-physical-transfer-bound-task.json'),recursive_task_sha256='b4495a8eee4deb1c6578820947eb2d0a1ca725813f1b380cbcf98c0712620a96',original_report_sha256='fe041ed219377b9aa5b13529511d655aa526f0e849c998b9ff30356dbd1f624d',original_i118_task_sha256='19806b3abe8937dbeb11fc72a8cb47a0c52d7bf2e7cee0a0880eefc2b5b2dbf1',normalization='Exact substring bytes, including delimiter-adjacent whitespace; report equality uses strip only for comparison.'))
# Record earlier completed readings. These are retrospective records, not claims of a second reading.
sys.path.insert(0,str(E));from read_support import record
C='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/'
retro=[
(str(S/'supplied-task.txt'),1,None),
(str(S/'snapshots/frontier/iterations/iteration121-physical-transfer-bound-task.json'),1,None),
(str(S/'original-i118-brief.txt'),1,None),
(str(S/'snapshots/frontier/iterations/i121-physical-transfer-bound.md'),1,None),
(str(S/'snapshots/frontier/experiments/i121-parent-verification.json'),1,None),
('AGENTS.md',1,None),('README.md',1,67),('frontier/iterations/i02-crossfield.md',1,259),
('frontier/iterations/i36-harmonic-analysis-discovery.md',1,45),
('frontier/reviews/i36-common-geometric-avoidance-r2.md',1,38),
('frontier/reviews/i36-common-geometric-avoidance-novelty-r3.md',95,125),
('frontier/iterations/i37-supergeometric-avoidance.md',1,74),
('frontier/iterations/i37-supergeometric-avoidance.md',265,300),
(C+'The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/build/sections/00_introduction.tex',1,245),
(C+'The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/build/sections/10_assembly.tex',1,613),
(C+'The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/build/sections/05_profiles_tests.tex',1,549),
(C+'The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/build/sections/08_recursion.tex',1,601),
(C+'The-Kakeya-maximal-conjecture-in-three-dimensions-September-23-2026/build/sections/80-consequences.tex',1,166),
(C+'The-weak-pinned-planar-distance-theorem-September-23-2026/build/sections/introduction.tex',1,217)]
for p,a,b in retro:
 if p=='README.md':p=str(S/'snapshots/README.md')
 with contextlib.redirect_stdout(io.StringIO()):record(p,a,b,scope='Retrospective binding of completed reading described in reading-notes.json; no second read claimed')
dump(S/'reading-notes.json',dict(recursive_reading='Full 119383-character I118 nested brief read in four bounded blocks, full I121 task brief read in two subsequent bounded blocks plus initial segment; full original I121 and final parent supplied and frozen. JSON source wrapper is bound, with brief content read rather than escaped JSON prose.',earlier_full_operations=['Falconer introduction, regularization, relevant planar preparation proofs, full oscillatory conversion, graph, two-depth payment, assembly/reconstruction','K3/K4 exact contracts and full consequences','Liu v3 complete proof sections through theorem ending'],limited_contract_readings=['Borges-Ou-Palsson main star and graph contracts','Iosevich-Yavicoli main positive/dimension distinction','Iosevich-Liu-Xi theorem, local setup, good/bad interfaces and final deduction','finite pinned, finite higher-dimensional distances and unit-distance introductions'],not_claimed='No full semantic reading of 749 manuscripts or entire external BOP/IY/ILX proof. No fresh reading claim for inherited passage records. I36/I37 disposition interfaces only, not re-audit of those original proofs.',conventions='New TeX/Markdown/HTML-text ranges use splitlines; inherited PDF passages retain LF. Passage hashes join with LF and append no newline. Initial HTML representations retained from standard-library math-alttext-aware extraction; primary and representation bytes both bound. extract_html.py documents the later ILX extraction.'))
failures=[
 dict(event='Initial broad repository/search outputs and several combined reading calls exceeded display limits',disposition='No whole-output semantic-coverage claim. Required recursive records, source proof endings and selected interfaces reread in bounded calls; exact lexical results retained independently.'),
 dict(event='Combined BOP contract reading and Liu paragraph output truncated',disposition='BOP 112-180 and Liu 160-185 reread; full operations needed by selected route read through endings.'),
 dict(event='Guessed arXiv identifier 1605.02190 returned unrelated Gaussian-process paper',disposition='Excluded; no theorem or attribution uses it.'),
 dict(event='Initial finite companion filename guess raised StopIteration',disposition='Recovered exact original paths from complete corpus map and read their contracts.'),
 dict(event='Guessed i36-doubling-pattern-avoidance.md path missing',disposition='Recovered i36-harmonic-analysis-discovery.md and both exact review paths using rg --files.'),
 dict(event='I02 range 475-580 exceeded 551 lines and raised AssertionError before writing read record',disposition='Reread exact 475-551 ending.'),
 dict(event='Ledger regex eight matched substrings including weights and caused truncated output',disposition='Broad output not treated as full reading; exact membership preserved by overlap-search.json and relevant frozen ledger scopes used.'),
 dict(event='Original I112 closed-component invertibility and equal-zero-lambda normalization failures',disposition='Inherited unchanged, not repaired, not P112 counterexamples.'),
 dict(event='Physical transfer/expanding Runge and I37 supergeometric targets unresolved',disposition='Preserved parked; no new bound asserted.'),
 dict(event='Fresh abstract unpinning and uniform pin-energy shortcuts fail',disposition='Counterexamples and exact limits proved in I124 report; A remains unproved/unrefuted.')]
dump(S/'failure-log.json',failures)
# Exact bounded project-overlap expression; active reports are deliberately absent.
paths=['frontier/iterations/i02-crossfield.md','frontier/reviews/i02-crossfield-r2.md','frontier/iterations/i36-harmonic-analysis-discovery.md','frontier/reviews/i36-common-geometric-avoidance-r2.md','frontier/reviews/i36-common-geometric-avoidance-novelty-r3.md','frontier/iterations/i37-supergeometric-avoidance.md']+[str(S/'snapshots'/p) for p in ['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']]
pat=r'(?i)\b(?:I02|I36|I37|I118|I121|I124|pinned|pinning|Falconer|Kakeya|incidence|uniformity|TECHNICAL ONLY)\b';rx=re.compile(pat);results=[]
for p in paths:
 for i,l in enumerate(Path(p).read_text().splitlines(),1):
  ms=list(rx.finditer(l))
  if ms:results.append(dict(path=p,splitlines_line=i,text=l,spans=[list(m.span()) for m in ms]))
dump(S/'overlap-search.json',dict(paths=paths,expression=pat,results=results))
# Pin URLs for every selected corpus reading; corpus itself is not copied.
domain=json.loads(Path('frontier/sources/i112_inverse_boundary_discovery/search-domain.json').read_text());bylocal={x['local']:x for x in domain}
manifest=json.loads((S/'read-manifest.json').read_text())
selected=[]
for p in sorted({x['local'] for x in manifest['passages']}):
 if p in bylocal:
  d=bylocal[p];selected.append(dict(**d,url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+d['path']))
dump(S/'selected-source-bindings.json',selected)
queries=['pinned Falconer distance positive Lebesgue measure irregular pins 2026','site:arxiv.org pinned distance regular pins Liu 2026','site:arxiv.org star configurations fractal sets Borges Ou Palsson 2026','site:arxiv.org Riemannian distance 5/4 Iosevich Liu Xi','site:arxiv.org 2610.05500 pinned distance']
dump(S/'literature-screen.json',dict(queries=queries,mode='Primary pages browsed, current abs/versioned HTML frozen; not an exhaustive literature/nonexistence claim',versions={'liu':'2603.15328v3','bop':'2607.10574v1','iy':'2610.05500v1','ilx':'1909.05171v2','repair':'2608.28711v1'},stronger_scope_checks='Regular pins; arbitrary separated positive-mass star pieces; pinned Hausdorff/lower-box versus positive Lebesgue measure; Riemannian 5/4; no power from compactness.',excluded='1605.02190 unrelated guessed identifier'))
refs=set(paths[:6])|{'AGENTS.md','sources/upstream.json','sources/CONTENTS.md','frontier/iterations/iteration121-physical-transfer-bound-task.json','frontier/iterations/i121-physical-transfer-bound.md','frontier/experiments/i121-parent-verification.json','frontier/sources/i88_nonlinear_banach_discovery/search-domain.json'}
refs|={x['local'] for x in manifest['passages'] if not x['local'].startswith(str(S)+'/')}
refs-={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
dump(S/'immutable-references.json',[dict(path=p,sha256=H(Path(p).read_bytes())) for p in sorted(refs)])
print(json.dumps(dict(owned_preparation='complete',read_records=len(manifest['passages']),selected_corpus_files=len(selected),immutable_direct=len(refs),overlap_hits=len(results))))
