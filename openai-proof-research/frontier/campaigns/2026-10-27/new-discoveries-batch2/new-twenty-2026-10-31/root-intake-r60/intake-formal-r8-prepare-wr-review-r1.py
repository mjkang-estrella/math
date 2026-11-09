"""Root documentary verification of 338806 formal r8, consolidated kernel evidence, and preparation of an independent 341690 review; no root mathematics or Lean execution."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
F=P/'high-girth-ur-matching-formal-sol-r8';A=P/'expanded-corpus-r518';L=P/'widom-rowlinson-tisgm-source-review-sol-r1';assert not L.exists()
def jsonrows(q):
 out=[]
 for line in q.read_text(errors='replace').splitlines():
  try:v=json.loads(line)
  except ValueError:continue
  if isinstance(v,dict):out.append(v)
 return out

# Every documentary check precedes any root mutation.
m=read(F/'R8-MANIFEST.json');assert len(m['files'])==1059 and m['credit']==0 and m['scientific_status']=='HOLD' and m['strict_green_modules']==49
names=set()
for n,x in m['files'].items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
 q=F/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],n
fex=m['terminal_noncircular_exclusions'];assert set(fex)=={'R8-MANIFEST.json','r8_manifest_093.receipt.json','r8_manifest_093.output.txt'}
inventory=set()
for q in F.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(F)))
assert inventory==names|set(fex)
frozen(F,765)
assert sha(F/'TASK.txt')==read(ROOT/'high-girth-ur-matching-formal-r8-ready.json')['task_sha256']
failures={n+'.receipt.json':1 for n in ['r8_matching_compile_006','r8_matching_compile_008','r8_matching_kernel_009','r8_obstruction_compile_016','r8_ratio_kernel_027','r8_api_028','r8_ratio_kernel_031','r8_standard_compile_038','r8_standard_compile_040','r8_standard_kernel_041','r8_standard_compile_044','r8_standard_compile_046','r8_standard_compile_048','r8_standard_kernel_051','r8_lightmatch_compile_056','r8_lightmatch_kernel_061','r8_bridges_checkpoint_062','r8_cast_compile_064','r8_cast_kernel_068','r8_relabel_compile_071','r8_canonical_kernel_088','r8_canonical_checkpoint_089']}
failures['r8_ratio_compile_022.receipt.json']=245;failures['r8_matchbridge_compile_053.receipt.json']=250;failures['r8_maxima_kernel_078.receipt.json']=250
frec=receipts(F,failures);assert read(F/'r8_manifest_093.receipt.json')['exit']==0
pins=read(F/'PINS.json');result=read(F/'results/338806.json');base=read(F/'BASELINE.json')
assert result['formal_status']=='INCOMPLETE_49_GREEN_NO_LITERAL_ENDPOINT' and result['credit']==0 and result['scientific_status']=='HOLD' and result['technical_pass'] is False
for row in base['immutable_green_modules']:assert sha(F/'src'/(row['module']+'.lean'))==row['source_sha256'] and sha(F/'build'/(row['module']+'.olean'))==row['olean_sha256']
bn=[x['module'] for x in base['immutable_green_modules']];assert len(bn)==42
pairs=[('URMatchingSurvivorMatching','r8_matching_compile_011','r8_matching_kernel_012','SurvivorMatchingAxioms.txt'),('URMatchingSurvivorObstruction','r8_obstruction_compile_018','r8_obstruction_kernel_019','SurvivorObstructionAxioms.txt'),('URMatchingSurvivorGap','r8_gap_compile_034','r8_gap_kernel_035','SurvivorGapAxioms.txt'),('URMatchingInduceBridge','r8_induce_compile_057','r8_induce_kernel_058','URMatchingInduceBridgeAxioms.txt'),('URMatchingRelabel','r8_relabel_compile_073','r8_relabel_kernel_074','URMatchingRelabelAxioms.txt'),('URMatchingMatchingMaximumMap','r8_maxmap_compile_081','r8_maxmap_kernel_082','URMatchingMatchingMaximumMapAxioms.txt'),('URMatchingURMaximumMap','r8_urmax_compile_084','r8_urmax_kernel_085','URMatchingURMaximumMapAxioms.txt')]
assert [p[0] for p in pairs]==result['r8_certified'] and result['strict_green_modules']==bn+[p[0] for p in pairs]
trio={'propext','Classical.choice','Quot.sound'};green=[]
for module,cl,kl,axf in pairs:
 c=next(x for x in jsonrows(F/(cl+'.output.txt')) if x.get('stage')=='compile' and x.get('module')==module)
 k=next(x for x in jsonrows(F/(kl+'.output.txt')) if x.get('stage')=='check' and x.get('module')==module)
 assert c['exit']==k['exit']==read(F/(cl+'.receipt.json'))['exit']==read(F/(kl+'.receipt.json'))['exit']==0
 source=sha(F/'src'/(module+'.lean'));olean=sha(F/'build'/(module+'.olean'))
 assert c['source_sha256_before']==c['source_sha256_after']==k['source_sha256_before']==k['source_sha256_after']==source and c['olean_sha256_after']==k['olean_sha256_before']==k['olean_sha256_after']==olean
 assert c['argv'][0]==pins['lean_bin'] and all(x in c['argv'] for x in ['-j1','-M3500','-DwarningAsError=true']) and k['argv']==[pins['leanchecker_bin'],module]
 assert c['LEAN_PATH']==k['LEAN_PATH']==':'.join([str(F/'build')]+pins['upstream_lean_paths']) and c['LEAN_NUM_THREADS']==k['LEAN_NUM_THREADS']==1
 found=re.findall(r'depends on axioms: \[([^\]]*)\]',(F/'audit'/axf).read_text(errors='replace'));assert found,axf
 assert all({y.strip() for y in f.split(',')}<=trio for f in found),axf
 green.append(dict(module=module,source_sha256=source,olean_sha256=olean,compile=cl,checker=kl,axioms=axf,compile_receipt_sha256=sha(F/(cl+'.receipt.json')),checker_receipt_sha256=sha(F/(kl+'.receipt.json'))))
uncert={'URMatchingSurvivorRatio','URMatchingSurvivorCast','URMatchingStandardGraph','URMatchingStandardMatching','URMatchingSubgraphMatching','URMatchingRelabelMaxima','URMatchingCanonical'};assert uncert=={p.stem for p in (F/'src').glob('*.lean')}-set(result['strict_green_modules']) and not uncert&set(result['strict_green_modules'])
for q in F.glob('*.output.txt'):assert 'sorryAx' not in q.read_text(errors='replace'),q.name
for q in (F/'src').glob('*.lean'):assert not re.search(r'\bsorry\b|\bnative_decide\b|\bunsafe\b|^\s*axiom\b',q.read_text(),re.M),q.name
allrows=base['immutable_green_modules']+green;assert len(allrows)==49

rows=[];pat=re.compile(r"failed to read file '([^']+)'|failed to create thread|bad_alloc|INTERNAL PANIC: out of memory")
for lane in ['high-girth-ur-matching-formal-sol-r4','high-girth-ur-matching-formal-sol-r5','high-girth-ur-matching-formal-sol-r6','high-girth-ur-matching-formal-sol-r7','high-girth-ur-matching-formal-sol-r8','parking-strong-a2-formal-sol-r1']:
 for q in sorted((P/lane).glob('*.receipt.json')):
  rec=read(q)
  if rec['exit']==0 or q.name.startswith('terminal'):continue
  out=q.with_name(q.name[:-len('.receipt.json')]+'.output.txt');text=str(rec.get('stderr'))+(out.read_text(errors='replace') if out.exists() else '');mm=pat.search(text)
  if mm:rows.append(dict(lane=lane,label=q.name[:-len('.receipt.json')],kind='read_failure' if mm.group(1) else mm.group(0),file=mm.group(1).split('/lean/')[-1] if mm.group(1) else None,exit=rec['exit'],wall_s=rec.get('wall_s'),sampled_group_rss_peak_bytes=rec.get('sampled_group_rss_peak_bytes'),as_limit_bytes=rec.get('as_limit_bytes')))
assert rows and all(x['as_limit_bytes']==6*1024**3 for x in rows)
ev=dict(utc=now,count=len(rows),by_kind=dict(collections.Counter(x['kind'] for x in rows)),per_lane=dict(collections.Counter(x['lane'] for x in rows)),distinct_read_failure_files=sorted({x['file'] for x in rows if x['file']}),max_sampled_rss_bytes=max(x['sampled_group_rss_peak_bytes'] for x in rows),rows=rows,root_hypothesis='leanchecker memory-maps every olean in the import closure, so RLIMIT_AS of 6 GiB may be exhausted by virtual mappings while real memory stays below about 1.5 GiB. Inference from logs only; not directly tested. Root runs no Lean and raising the cap needs user authorization.',root_Lean_execution=False)
save(ROOT/'kernel-read-failure-evidence-r8.json',ev)

fs='338806 uncredited formal r8 INCOMPLETE, no literal negation, no paper, no technical PASS. Seven new strict compile plus kernel green modules with scoped axioms verified byte/log/receipt on top of forty-two sealed baseline modules, forty-nine in all: actual first-colour matching on the induced survivor with 100|M|>99N; all actual survivor UR matchings give empty rectangles, so nu_ur<2a; the natural strict gap 4 nu_ur<3 nu at every cutoff h for a degree-100 induced survivor; induced graph equals standard G.induce; relabeling preserves matchings, covered sets and literal UR uniqueness across universes; and both maxima are invariant under adjacency equivalence. Compiled or attempted but NOT certified: SurvivorRatio, SurvivorCast, StandardGraph, SubgraphMatching, RelabelMaxima and Canonical all failed their kernel checks, and StandardMatching failed to compile. Every remaining mathematical step is blocked at the same resource wall: genuine Walk.IsCycle and girth, the real ratio, standard degree and matching correspondences, canonical coding and the universal negation. Root pauses this chain pending a user decision on the address-space cap, rather than launching another round. Scientific HOLD and credit 0 unchanged, 57/60. 1059 manifest files, 765 frozen bindings, 49 modules verified; no root Lean execution.'
fr=dict(utc=now,mathdb_id=338806,source_lane=str(F),manifest_sha256=sha(F/'R8-MANIFEST.json'),verified_manifest_files=1059,verified_frozen_bindings=765,green_modules=allrows,new_green_modules=green,not_kernel_green=sorted(uncert),runner_receipts=frec,body_audit_unpaid=True,result=result,scientific_summary=fs,root_disposition='INCOMPLETE_UNCREDITED_FORMAL_RESEARCH_PAUSED_PENDING_USER_RESOURCE_DECISION',credit=0,accepted_new=57,terminal_self_exclusions=fex,root_scope='Documentary integrity only; no Lean/math execution by root.')
den=read(ROOT/'inherited-denials-r542.json');den['utc']=now;den['root_highgirth338806_formal_r8_scope']=fs
save(P/'high-girth-ur-matching-formal-parent-integration-r8.json',fr);denpath=ROOT/'inherited-denials-r543.json';save(denpath,den)
save(ROOT/'formal-r8-intake-report.json',dict(utc=now,files=1059,frozen=765,verified_green_modules=allrows,not_kernel_green=sorted(uncert),paused=True,credit=0,accepted_new=57,no_root_mathematics=True))

gates=read(A/'results.json');v=read(A/'originals/341690-provenance.json');raw,literal,token=corpus(v);assert (A/'originals/341690.jsonl').read_bytes()==raw and literal['mathdb_id']==341690
L.mkdir();(L/'inputs').mkdir()
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json','charge_search.py']:shutil.copyfile(A/h,L/h)
shutil.copyfile(denpath,L/'inherited-denials.json')
(L/'inputs/original341690.raw.jsonl').write_bytes(raw);save(L/'inputs/literal341690.json',literal);save(L/'inputs/provenance341690.json',v);save(L/'inputs/author-gates341690.json',gates['341690'])
for f in ['FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','ACTUALBRIEF.md','NEW-UNAVAILABLE.json','access-inventory.json','search1-response.json','search2-response.json','search3-response.json','get-wr.json','get-wr-meta.json','get-wr-final.json']:shutil.copyfile(A/f,L/'inputs'/f)
for f in ['wr.pdf','wr.txt','wr-meta.html']:shutil.copyfile(A/'sources'/f,L/'inputs'/f)
shutil.copyfile(ROOT/'accepted57-review-context.json',L/'inputs/accepted57-scopes.json')
prior=P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json';assert sha(prior)=='6493e29137d286242b09d96f97dfe39a9ca5146a8d73bcfa8177e4705d6aaff3';shutil.copyfile(prior,L/'inputs/prior39-scopes.json')
save(L/'reservation.json',dict(ids=[341690],rows=[literal],purpose='Independent ordinary proof, literal/source, prior-art and significance review of the Widom-Rowlinson exact TISGM count proposal; no formal tools'))
(L/'reservation.sha256').write_text(sha(L/'reservation.json')+'  reservation.json\n');save(L/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
t=ast.parse((ROOT/'prepare-covariance-planar-reviews-r506.py').read_text());common=next(ast.literal_eval(x.value) for x in t.body if isinstance(x,ast.Assign) and any(isinstance(y,ast.Name) and y.id=='COMMON' for y in x.targets))
detail='''TARGET: MathDB 341690, the exact TISGM count conjecture for the ferromagnetic hard-core and soft-core Widom-Rowlinson model on Cayley trees. Primary source: Kissel, Kuelske and Rozikov, arXiv 1901.09258v1, supplied as inputs/wr.pdf (wr.txt is extraction only). The original raw record is inputs/original341690.raw.jsonl.

READ FIRST. inherited-denials.json is about 250 KB and TASK.txt is long. Straight after the two mandatory commands, read both COMPLETELY in contiguous chunks of at most 15000 characters and record the ranges. Save every native search response in the very next tool call after it returns, before any other step.

The author FULLCANDIDATE.md is an unreviewed proposal and also contains the unrelated 336276; ignore that part. Root has verified provenance only, with a hand spot check of the elimination leading to equation (A) that does not replace yours. Disclosed mechanism: the diagonal solution is unique by monotonicity; an off-diagonal solution is parametrized by the ratio t=u/v, giving lambda=L(t); with t=exp(2s), strict convexity of b*coth(bs) makes L strictly increasing on its whole domain, so one branch gives exactly two off-diagonal solutions above a threshold. Reconstruct the proof or a precise GAP yourself before opening FULLCANDIDATE.md or DORMANT-SOL-FORMAL-PLAN.md.

LITERAL AND SOURCE BINDING. Settle each from the actual glyphs, not from the author's summary:
1. The literal refers to parts 2) and 3) of the preceding theorem and to theta'_c(k), lambda'_cr(k), theta_c(k) and lambda_cr(k). Render and view Theorem 6 and Conjecture 1, and write out exactly which parameter regions parts 2) and 3) cover. Confirm that the proposal's partition by theta_c=(k-1)/(k+1) and lambda_c reproduces those regions exactly, including boundary values, and that nothing is silently dropped or added. Remark on any inconsistency in the source's critical values.
2. Decide what "ferromagnetic" means in the source: confirm the range of theta and the role of theta=0 (hard-core), and whether k>=4 is a real restriction in the literal.
3. The literal counts translation-invariant splitting Gibbs measures, not equation roots. Check the source's boundary-law theorem and the proposal's bridge in both directions: each positive constant normalized boundary law gives a TISGM, distinct laws give distinct measures, and every TISGM arises so, including the theta=0 hard-core constraint where some transitions vanish.

ORDINARY AUDIT. Check at least: the reduction from (4.1) to (4.9) and the kth-root parametrization; uniqueness of the diagonal solution for every parameter; the elimination giving D(t) and (A), with every denominator positive and reversibility; the exact domain of t, including the sign of D, the empty-domain case theta>=theta_c and theta=0; the sinh form (B); positivity of f' and f'' and the convexity secant estimate for every k>=4 with its sum range; the monotonicity of R and of the factor 1/(1-theta/R); both endpoint limits and the critical equality case lambda=lambda_c; and the claim that off-diagonal solutions come in swap pairs so the total is exactly three.

SOURCE CLOSURE AND PRIOR ART. The entire work 1901.09258 and its JSTAT 2019 final, DOI 10.1088/1742-5468/ab081e, are closed to all new deliveries after a verification page; do not retry or recover it by any route. The cached v1 is not final-equivalence evidence, so record a source-final HOLD and assess how much it matters given the MathDB literal. Exact-count results for hard-core and Widom-Rowlinson type models on trees are a substantial literature. Use your search budget on distinct primary sources, including the hard-core hinge and wand all-k exact-critical result that the author flagged as unread, and later work by Rozikov, Kuelske or others on SCWR counts. If an applicable theorem exists, give the complete bridge. A bounded nonmatch is not a worldwide novelty claim.

SIGNIFICANCE. Campaign policy gives zero credit to routine corollaries, routine adaptations, parameter instances and known results, and shortness alone is not an exclusion. Give the strongest case on each side. Negative: a one-variable branch analysis of a two-variable recursion may be standard for this literature, and the ratio parametrization may already appear for related models. Positive: the source leaves exact counts and part of the parameter region explicitly conjectural after its own methods stop, and the proof is a global count by a new convexity argument rather than one changed estimate. Say plainly how much of this argument, if any, is already in the source. End with one recommendation: CREDITABLE SUBJECT TO LEAN AND PAPER, PARK, or EXCLUDE AS ROUTINE OR KNOWN, with reasons. Root alone adjudicates.

FAMILY AND FORMAL. Compare against all supplied 57+39 scopes. Do not run Lean. Record which formal infrastructure is unpaid, in particular Gibbs measures on infinite trees and the boundary-law bijection, as opposed to the one-variable real analysis, and give a realistic feasibility estimate, noting that heavy imports are currently hard to kernel-check here. Write a dormant Sol formal brief only if the scientific gates prospectively survive.

Author proposal is not an independent PASS. Credit 0; campaign 57/60 unchanged.
'''
peers=['simplex-three-design-source-review-sol-r1','interval-kwidth-formal-sol-r1'];task=common.format(lane=L,id=341690,peers=', '.join(peers))+'\nTARGET-SPECIFIC INDEPENDENT REVIEW\n'+detail
(L/'TASK.txt').write_text(task);ff=[q for q in L.iterdir() if q.is_file() and q.name!='search-budget.json']+list((L/'inputs').iterdir());save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),mathdb_id=341690,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=peers,latest_denials=str(denpath))
save(ROOT/'widom-rowlinson-review-r1-ready.json',ready);save(ROOT/'selection-routing-widom-rowlinson-review-r1.json',dict(ids=[341690],sources=[literal['source_url']],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True))
print(json.dumps(dict(r8_manifest=1059,frozen=765,green=len(allrows),not_kernel_green=sorted(uncert),evidence=dict(count=ev['count'],by_kind=ev['by_kind'],distinct=len(ev['distinct_read_failure_files']),max_rss=ev['max_sampled_rss_bytes'],per_lane=ev['per_lane']),review=ready,credit=0,accepted_new=57)))
