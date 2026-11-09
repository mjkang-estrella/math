"""Root documentary verification of 336276 formal r2 and preparation of a second adversarial prior-art and significance qualification; no root mathematics or Lean execution."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
F=P/'interval-kwidth-formal-sol-r2';V=P/'interval-kwidth-limit-source-review-sol-r1';L=P/'interval-kwidth-primary-qualification-sol-r2';assert not L.exists()
def jsonrows(q):
 out=[]
 for line in q.read_text(errors='replace').splitlines():
  try:v=json.loads(line)
  except ValueError:continue
  if isinstance(v,dict):out.append(v)
 return out

# Every documentary check precedes any root mutation.
m=read(F/'MANIFEST.json');assert len(m['files'])==341==m['count']
names=set()
for n,x in m['files'].items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
 q=F/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],n
fex=m['terminal_non_circular_exclusions'];assert set(fex)=={'MANIFEST.json','seal_manifest28.output.txt','seal_manifest28.receipt.json'}
inventory=set()
for q in F.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(F)))
assert inventory==names|set(fex)
frozen(F,184)
assert sha(F/'TASK.txt')==read(ROOT/'interval-kwidth-formal-r2-ready.json')['task_sha256']
failures={n+'.receipt.json':1 for n in ['balanced_first','balanced_compile2','balanced_compile3','counts_compile7','algebra_compile10','algebra_kernel12','algebra_smaller_kernel14','controls_compile20','negative23']}
frec=receipts(F,failures);assert read(F/'seal_manifest28.receipt.json')['exit']==0 and read(F/'replay25.receipt.json')['exit']==0
pins=read(F/'PINS.json');result=read(F/'results/336276.json');base=read(F/'BASELINE.json')
assert result['credit']==0 and result['status']=='FINITE_ONLY_PARTIAL_KERNEL_BLOCKED_ZERO_CREDIT' and result['literal_endpoint_proved'] is False and result['compile_only_uncertified_modules']==['IntervalBlockAlgebra'] and result['source_only_replay']['modules']==18
for row in base['immutable_green_modules']:assert sha(F/'src'/(row['module']+'.lean'))==row['source_sha256'] and sha(F/'build'/(row['module']+'.olean'))==row['olean_sha256']
bn=[x['module'] for x in base['immutable_green_modules']];assert len(bn)==13
pairs=[('IntervalBalanced','balanced_fix4','balanced_kernel5'),('IntervalBlockCounts','counts_fix8','counts_kernel9'),('IntervalFiniteGrid','grid_complete16','grid_kernel17'),('IntervalGridAdditive','additive_compile18','additive_kernel19'),('IntervalFiniteControls','controls_fix21','controls_kernel22')]
assert result['strict_green_modules']==bn+[p[0] for p in pairs]
trio={'propext','Classical.choice','Quot.sound'};green=[]
for module,cl,kl in pairs:
 c=next(x for x in jsonrows(F/(cl+'.output.txt')) if x.get('stage')=='compile' and x.get('module')==module)
 k=next(x for x in jsonrows(F/(kl+'.output.txt')) if x.get('stage')=='check' and x.get('module')==module)
 assert c['exit']==k['exit']==read(F/(cl+'.receipt.json'))['exit']==read(F/(kl+'.receipt.json'))['exit']==0
 source=sha(F/'src'/(module+'.lean'));olean=sha(F/'build'/(module+'.olean'))
 assert c['source_sha256_before']==c['source_sha256_after']==k['source_sha256_before']==k['source_sha256_after']==source and c['olean_sha256_after']==k['olean_sha256_before']==k['olean_sha256_after']==olean
 assert c['argv'][0]==pins['lean_bin'] and all(x in c['argv'] for x in ['-j1','-M3500','-DwarningAsError=true']) and k['argv']==[pins['leanchecker_bin'],module]
 assert c['LEAN_PATH']==k['LEAN_PATH']==':'.join([str(F/'build')]+pins['upstream_lean_paths']) and c['LEAN_NUM_THREADS']==k['LEAN_NUM_THREADS']==1
 text=(F/(cl+'.output.txt')).read_text(errors='replace');assert 'sorryAx' not in text and 'sorry' not in (F/'src'/(module+'.lean')).read_text(),module
 found=re.findall(r'depends on axioms: \[([^\]]*)\]',text);assert all({y.strip() for y in f.split(',')}<=trio for f in found),module
 green.append(dict(module=module,source_sha256=source,olean_sha256=olean,compile=cl,checker=kl,compile_receipt_sha256=sha(F/(cl+'.receipt.json')),checker_receipt_sha256=sha(F/(kl+'.receipt.json'))))
sorry_logs=[q.name[:-len('.output.txt')] for q in F.glob('*.output.txt') if 'sorryAx' in q.read_text(errors='replace')]
assert sorry_logs and all(read(F/(l+'.receipt.json'))['exit']!=0 for l in sorry_logs),sorry_logs
for q in (F/'src').glob('*.lean'):assert not re.search(r'\bsorry\b|\bnative_decide\b|\bunsafe\b|^\s*axiom\b',q.read_text(),re.M),q.name
allrows=base['immutable_green_modules']+green;assert len(allrows)==18
fs='336276 formal r2 INCOMPLETE, credit 0, no literal endpoint. Five new finite strict compile plus kernel green modules verified byte/log/receipt on top of thirteen sealed modules, eighteen in all, with all eighteen passing a fresh source-only empty-build replay: balanced consecutive blocks and chronological labels, the block-count decomposition, the all-cut bound in exact additive natural form from actual suffix heights, the deterministic finite-grid envelope for monotone counts over an ordered additive monoid, and finite controls. IntervalBlockAlgebra (generic-ring telescoping, completing the square and block error bound) strictly compiled in two genuinely different import graphs but its kernel check failed loading upstream Order/GroupWithZero/Canonical and Tactic/Ring/Common, so it is NOT certified and quantitative inequality (E) is unpaid. sorryAx appears only in three failed compile logs, where Lean marks declarations that did not elaborate; none is in a certified module. Every remaining step needs ring tactics, fields, reals or measures, so this chain is paused at the same kernel-check wall. Prospective scientific pass unchanged. 341 manifest files, 184 frozen bindings, 18 modules verified; no root Lean execution. Credit 0, 57/60.'
fr=dict(utc=now,mathdb_id=336276,source_lane=str(F),manifest_sha256=sha(F/'MANIFEST.json'),verified_manifest_files=341,verified_frozen_bindings=184,green_modules=allrows,new_green_modules=green,not_kernel_green=['IntervalBlockAlgebra','IntervalSampling','IntervalLiteral'],sorry_only_in_failed_logs=sorted(sorry_logs),source_only_replay_receipt_sha256=sha(F/'replay25.receipt.json'),runner_receipts=frec,result=result,scientific_summary=fs,root_disposition='INCOMPLETE_FORMAL_RESEARCH_PAUSED_AT_KERNEL_WALL',credit=0,accepted_new=57,terminal_self_exclusions=fex,root_scope='Documentary integrity only; no Lean/math execution by root.')
den=read(ROOT/'inherited-denials-r549.json');den['utc']=now;den['root_interval336276_formal_r2_scope']=fs
save(P/'interval-kwidth-formal-parent-integration-r2.json',fr);denpath=ROOT/'inherited-denials-r550.json';save(denpath,den)

L.mkdir();(L/'inputs').mkdir()
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json','charge_search.py']:shutil.copyfile(V/h,L/h)
shutil.copyfile(denpath,L/'inherited-denials.json')
for q in sorted((V/'inputs').iterdir()):
 if q.is_file():shutil.copyfile(q,L/'inputs'/q.name)
for f in ['REVIEW.md','PROOF.md','review.json','source-map.json','family-comparison.json','search1-full-response.json','search2-full-response.json']:shutil.copyfile(V/f,L/'inputs'/('review-r1-'+f))
for f in ['companion.pdf','companion.txt','streaming.pdf','streaming.txt']:shutil.copyfile(V/'sources'/f,L/'inputs'/f)
literal=read(L/'inputs/literal336276.json')
save(L/'reservation.json',dict(ids=[336276],rows=[literal],purpose='Second adversarial prior-art and significance qualification of the random-interval k-width limit; no formal tools'))
(L/'reservation.sha256').write_text(sha(L/'reservation.json')+'  reservation.json\n');save(L/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
t=ast.parse((ROOT/'prepare-covariance-planar-reviews-r506.py').read_text());common=next(ast.literal_eval(x.value) for x in t.body if isinstance(x,ast.Assign) and any(isinstance(y,ast.Name) and y.id=='COMMON' for y in x.targets))
detail='''TARGET: second adversarial qualification of MathDB 336276, the random-interval k-width limit E[k-width]/n -> 1/(k+1) for every fixed k>=2. The first review, inputs/review-r1-REVIEW.md and inputs/review-r1-PROOF.md, passed the ordinary proof and model and recommended CREDITABLE SUBJECT TO LEAN AND PAPER, with bounded prior-art search. Three other candidates in this campaign looked similarly good after a first review and were then excluded when a deeper prior-art or generalization check showed they were routine. Your job is to try hard to do the same here, and to report honestly if you cannot.

READ FIRST. inherited-denials.json is over 250 KB and TASK.txt is long. Straight after the two mandatory commands, read both COMPLETELY in contiguous chunks of at most 15000 characters and record the ranges. Save every native search response in the very next tool call after it returns, before any other step.

PROOF. Read inputs/review-r1-PROOF.md critically and check each step. For this second review that satisfies the reconstruction requirement in the common text. Report any error, but do not spend effort re-deriving what is already paid.

CLOSED ROUTES. The official author page https://tcs.ieat.ro/members/gistrate/ is closed. Distinct Istrate papers are not closed. Before every GET, consider whether the host might redirect to a blocked route; a rejected redirect ends your network work, so prefer direct arXiv or open institutional PDF URLs you actually observed. Do not use Citeseer or Wayback.

THE ADVERSARIAL QUESTIONS. Answer each concretely, with primary sources where they exist:
1. Is this limit a direct consequence of a known general theorem? Look specifically at fluid limits and laws of large numbers for matchings or b-matchings in random graphs and random bipartite graphs with a geometric or monotone structure; Hall-type or Koenig-type minimax formulas with uniform laws of large numbers over staircase or monotone cuts, for example VC or bracketing arguments; Greene-Kleitman and Dilworth-type theorems and chain or antichain partitions in random interval orders; Hammersley-type process hydrodynamics; online or chronological matching limits. If a theorem applies, give the complete bridge to the literal.
2. Independently of any citation, say how hard the upper bound is. The all-cut block envelope is essentially a uniform law of large numbers over a low-complexity family of time-position staircases. Would a specialist regard that as a routine discretization, or does the chronological constraint do real work that a generic argument would miss? Try writing the shortest generic proof you can, and say precisely which step, if any, is not routine.
3. Does the set version, or any k=1 or sequence version in the Hammersley or heapability literature, already contain the same computation? Look for follow-up papers on heapability of sequences, partial orders and random intervals, including journal versions of the companion paper and later citations of the source.
4. Is the constant 1/(k+1) obtainable from the source's own Theorem and a one-line threshold optimization, with the matching upper bound being the only remaining content? Say how much of the result is actually new relative to the source.
If you find an applicable theorem or a complete routine reduction, recommend exclusion and give the bridge. If you cannot after a real attempt, say so and say what the bounded search did and did not cover. A bounded nonmatch is not a worldwide novelty claim.

SIGNIFICANCE. Campaign policy gives zero credit to routine corollaries, routine adaptations, known results and parameter instances, and shortness alone is not an exclusion. Give the strongest case on each side, informed by your answers. End with one recommendation: CREDITABLE SUBJECT TO LEAN AND PAPER, PARK, or EXCLUDE AS ROUTINE OR KNOWN, with reasons. Root alone adjudicates.

FAMILY AND FORMAL. The first review compared all 96 supplied scopes; spot-check that comparison rather than repeating it. Do not run Lean. Eighteen finite Lean modules exist in a protected lane and are not your concern.

Author proposal and first review are not acceptance. Credit 0; campaign 57/60 unchanged.
'''
peers=['expanded-corpus-r522','expanded-corpus-r523'];task=common.format(lane=L,id=336276,peers=', '.join(peers))+'\nTARGET-SPECIFIC SECOND QUALIFICATION\n'+detail
(L/'TASK.txt').write_text(task);ff=[q for q in L.iterdir() if q.is_file() and q.name!='search-budget.json']+list((L/'inputs').iterdir());save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
rdy=dict(utc=now,lane=str(L),mathdb_id=336276,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=peers,latest_denials=str(denpath))
save(ROOT/'interval-kwidth-qualification-r2-ready.json',rdy);save(ROOT/'selection-routing-interval-kwidth-qualification-r2.json',dict(ids=[336276],sources=[literal['source_url']],lane=str(L),task_sha256=rdy['task_sha256'],metadata_only=True))
print(json.dumps(dict(formal_manifest=341,frozen=184,green=len(allrows),sorry_only_in_failed=sorted(sorry_logs),qualification=rdy,credit=0,accepted_new=57)))
