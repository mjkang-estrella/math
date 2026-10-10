"""One-time focused evidence preparation. Never executes ancestor programs."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i159_oracle_tolerance_focused_r3'
E=ROOT/'frontier/experiments/i159_oracle_tolerance_focused_r3'
REPORT=ROOT/'frontier/reviews/i159-oracle-tolerance-focused-r3.md'
assert not (S/'seal.json').exists(), 'Already sealed; no repair/reseal permitted'
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def bind(p,role):
 b=(ROOT/p).read_bytes();return {'path':p,'sha256':sha(b),'bytes':len(b),'role':role}
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
base='preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026'
local='frontier/sources/i14_spectral_width_novelty_r3/corpus/'
tree=json.loads((ROOT/'sources/preprints-tree.json').read_text());assert tree['truncated'] is False
index={r['path']:r for r in tree['tree']}
spec={
 'introduction':('model and scope',[], 'original-class; main upper assertion only'),
 'preliminaries':('primitive interface; C2 comparisons; moments; conditional couplings',[], 'primitive; convex-preliminaries; primitive-moments; coupling-smoothing'),
 'jets':('Gaussian conditional smoothing and transport',['preliminaries'],'conditional-tilt; appell-cumulants; gaussian-jets; transport'),
 'divergence':('material, split and RMS operations',['jets','preliminaries'],'material-identities; split-contraction; tensor-divergence; divergence-l2; path-derivatives'),
 'centering':('ideal noisy mean and derivative controls',['jets','divergence','preliminaries'],'transport-derivatives; centering-kernel; centering-law; stationary-derivatives'),
 'numerics':('actual affine row sums, scales, accuracy and depth',['preliminaries','jets','divergence','centering'],'probability-circuit; kernel-angle-errors; kernel-endpoint-quadrature; kernel-circuit; mean-circuit; exact-mean-circuits; numerical-interface'),
 'implementation':('actual finite compiler and intrinsic standalone accuracy',['preliminaries','numerics'],'compiler-absorption; compiler-height; compiler-count; compiler-terminal; compiler-sizes; compiler-lipschitz; compiler-accuracy; primitive'),
 'sampling':('physical kernel, moments, descent, terminal rule and caps',['preliminaries','implementation'],'proximal-contraction; proximal-local-errors; descent-moments; conditional-descent; mode-iteration; mode-gaussian; descent-base-error; upper-query-count')}
deps=[]
for name,(role,parents,labels) in spec.items():
 rel=base+'/build/sections/'+name+'.tex';p=local+rel;b=(ROOT/p).read_bytes();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert blob==index[rel]['sha']
 deps.append({**bind(p,role),'source_path':rel,'git_blob':blob,'pinned_url':f'https://raw.githubusercontent.com/openai/math/{PIN}/{rel}','depends_on':parents,'labels':labels.split('; '),'complete_new_read':True,'lines':len(b.decode().splitlines()),'boundary':'Stipulated theorem AND lower proof operations; applicability reviewed, not truth-audited'})
primary='frontier/sources/i154_dimension_independent_oracle_tolerance/primary/'
retrieval=json.loads((ROOT/(primary+'retrieval.json')).read_text());receipts=[r for r in retrieval if r['url'] in ['https://arxiv.org/abs/2311.14520','https://arxiv.org/pdf/2311.14520']]
for r in receipts:
 assert sha((ROOT/r['path']).read_bytes())==r['sha256']
 if 'text_path' in r:assert sha((ROOT/r['text_path']).read_bytes())==r['text_sha256']
dump(S/'dependencies.json',{'pin':PIN,'sources':deps,'external_proof':{'name':'Shifted Composition I','receipts':receipts,'application':'KL/W2 nonexpansive specialization with the original explicit theta schedule; not optimized shifts or Renyi','independent_derivation':'review report equations (9)-(12)','read_range_convention':'Python splitlines; form feeds can change line numbers from LF-only ancestor receipts','relevant_read_end':606,'external_companion_required':False},'excluded':{'source_lower_bound':'No mathematical edge to R154 upper bound','comparators':'Shifted III, inaccurate-gradient LMC, Picard, stochastic-oracle and cloud proofs do not supply a premise of equations (1)-(19); contribution gate deferred','historical_branches':'No new torus, weighted-bin, trace-decoder, PDE or older parked-branch audit'},'missing_actual_dependencies':[]})
refs={x['path']:x['role'] for x in deps}
refs.update({'AGENTS.md':'project instructions','sources/upstream.json':'pinned revision','sources/preprints-tree.json':'immutable source-path/Git-blob map; only focused entries checked','sources/CONTENTS.md':'catalogue pointer, not theorem evidence'})
expected={152:'f13a8eb19fe9ee8cdd1a6fbeb6618529a48c0599f08a84272be5b68570bf7379',154:'0fa43c233f6032d38f3b905cac2253321303e3a300342112ae8716e504897d97',157:'b6975be60991316c0d845e3f3e4541f8c3fb66addca871f7d109a5ee423a0940'}
context=[]
for n in (152,154,157):
 p=next((ROOT/'frontier/iterations').glob(f'iteration{n}-*task.json'));assert sha(p.read_bytes())==expected[n];j=json.loads(p.read_text());refs[str(p.relative_to(ROOT))]='unchanged original task; all fields retained, scoped semantic coverage distinguished'
 fields=[]
 def walk(x,path='$'):
  if isinstance(x,dict):
   for k,v in x.items():yield from walk(v,path+'.'+k)
  elif isinstance(x,list):
   for k,v in enumerate(x):yield from walk(v,path+f'[{k}]')
  else:
   fields.append({'path':path,'type':type(x).__name__,'value_sha256':sha(str(x).encode())});yield f'FIELD {path}\n{x}\nEND FIELD {path}\n'
 stream=''.join(walk(j));assert (S/f'task{n}-decoded.txt').read_text()==stream
 parent=f'frontier/experiments/i{n}-parent-verification.json';refs[parent]='finalized original parent response, context only; no program executed'
 assert json.loads((S/f'parent{n}-review.json').read_text())==json.loads((ROOT/parent).read_text())['parent_review']
 context.append({'iteration':n,'original':str(p.relative_to(ROOT)),'sha256':expected[n],'decoded':str((S/f'task{n}-decoded.txt').relative_to(ROOT)),'fields':fields,'coverage':('Complete historical I157 brief and included I154 report/audit/parent supplied in current user task; new local original report/audit/parent reads separately logged; launch metadata displayed.' if n==157 else 'All fields retained; direct briefs, R152 sampling chain and parent responses inspected; unrelated recursive semantic audit remains incomplete and is not a condition of the focused gate.')})
for p,role in {
 'frontier/iterations/i152-algorithmic-sampling-reconstruction-discovery.md':'original R1-R4 historical proof; relevant occurrences embedded in I154 task',
 'frontier/iterations/i154-dimension-independent-oracle-tolerance.md':'unchanged theorem/proof under review',
 'frontier/sources/i154_dimension_independent_oracle_tolerance/original-audit-report.md':'original scoped verdict history and preserved failures',
 'frontier/reviews/i157-dimension-independent-oracle-tolerance-r2.md':'prior incomplete findings, challenged not authoritative',
 'frontier/sources/i157_dimension_independent_oracle_tolerance_r2/clarifications.md':'prior clarifications, independently checked against original',
 'frontier/sources/i157_dimension_independent_oracle_tolerance_r2/review-status.json':'historical incomplete status',
 'frontier/sources/i157_dimension_independent_oracle_tolerance_r2/reading-notes.json':'preserved historical failed/truncated attempts; not inherited semantic credit',
 'frontier/sources/i157_dimension_independent_oracle_tolerance_r2/primary-web.json':'historical failed journal web attempt; context only',
 primary+'shifted1.pdf':'bound primary PDF; no re-extraction or new rendering',
 primary+'shifted1.txt':'actual external operative proof read',
 primary+'shifted1.html':'primary version record',
 primary+'retrieval.json':'original primary retrieval receipt, not mathematical authority'}.items():refs[p]=role
occ=[]
for n,p in [(157,'frontier/iterations/i154-dimension-independent-oracle-tolerance.md'),(157,'frontier/sources/i154_dimension_independent_oracle_tolerance/original-audit-report.md'),(154,'frontier/iterations/i152-algorithmic-sampling-reconstruction-discovery.md')]:
 task=next((ROOT/'frontier/iterations').glob(f'iteration{n}-*task.json'));brief=json.loads(task.read_text())['brief'];t=(ROOT/p).read_text().rstrip();at=brief.find(t);assert at>=0
 occ.append({'task':str(task.relative_to(ROOT)),'field':'brief','start_unicode':at,'end_unicode':at+len(t),'source':p,'normalization':'source text rstrip only','substring_sha256':sha(t.encode())})
dump(S/'context-coverage.json',{'scope_change':'Current user explicitly limits completeness gate to original R154 and all its actual mathematical dependencies. Historical I157 broader audit remains INCOMPLETE.','tasks':context,'embedded_original_occurrences':occ,'new_local_reads':'read-log.json; not an inherited full-read assertion','supplied_context':'Full original I157 and direct I154 briefs, full I154 report/audit/parent, full I157 findings and finalized parent supplied in user message; read as context.','older_recursive_semantic_audit_complete':False,'no_full_corpus_semantic_reread':True,'no_old_evidence_replay':True})
ledgers=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'];snaps=[]
for p in ledgers:
 b=(ROOT/p).read_bytes();dest=S/'snapshots'/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b);snaps.append({'live_path':p,'snapshot':str(dest.relative_to(ROOT)),'sha256':sha(b),'scope':'snapshot only; incidental mentions do not bind active project artifacts'})
dump(S/'snapshots.json',snaps)
oldnotes=json.loads((ROOT/'frontier/sources/i157_dimension_independent_oracle_tolerance_r2/reading-notes.json').read_text())
dump(S/'attempts.json',{'new_attempts':[
 {'kind':'wrong cwd','error':'cat: sources/upstream.json: No such file or directory; subsequent rg/ls likewise failed','resolution':'Repeated with explicit /home/mj-kang/Documents/Dev/math/openai-proof-research working directory; successful.'},
 {'kind':'bounded discovery','details':'Initial rg file list used head -80. Source-binding exploratory JSON displayed first 10000 characters. Neither is a complete read claim. Required sampling source files subsequently read completely.'},
 {'kind':'truncated output','details':'Combined task-heading search, shifted1 line search and introduction 1-165 display: tool reported 12839 original tokens and output truncation. Middle search listing truncated; no whole-task semantic credit. Introduction 1-165 itself visible completely; 166-269 displayed separately. Required source/brief readings credited by explicit receipts or supplied context.'},
 {'kind':'invalid range','error':'parent154-review.json requested 90-158 but contains 105 lines; AssertionError before read receipt','resolution':'Recovered by complete 1-105 display.'},
 {'kind':'bounded metadata inspection','details':'Exploratory retrieval and primary-web prefixes were displayed with character limits. No full-read credit; exact selected shifted1 receipt is validated by preparation/replay.'}
 ],'inherited_attempts_preserved':oldnotes['truncated_or_failed_displays'],'inherited_failed_journal_attempt':oldnotes['primary_metadata']['shifted3_journal_attempt'],'journal_dependency_for_current_proof':False,'ancestor_programs_executed':0,'corpus_copies':0,'inherited_pdf_reextractions':0})
dump(S/'primary-check.json',{'date':'2026-10-10','url':'https://arxiv.org/abs/2311.14520','new_live_check':'web open successful; metadata says v1 submitted 24 November 2023, Altschuler and Chewi','role':'metadata only; proof bound by immutable local text/PDF','proof_endings':'Theorems 3.1/3.2 and Lemma 3.6/Theorem 3.7 completely read; original schedule avoids appendix optimization; no reliance on later refinements','comparison_scope':'No new contribution decision'})
dump(S/'review-status.json',{'iteration':159,'scope':'ORIGINAL R154 theorem and all actual mathematical dependencies','verdict':'PASS without substantive repairs','review_complete_at_this_scope':True,'historical_I157_broad_audit':'INCOMPLETE; original verdict unresolved','historical_internal_reserve_assertion':'FAIL','equations_independently_rebuilt':list(range(1,20)),'substantive_repairs':[],'unpaid_actual_mathematical_dependencies':[],'external_comparator_audit_complete':False,'contribution_decision':None,'acceptance_decision':None,'accepted':8,'remaining':2,'original_bytes_changed':False,'children':0,'ancestor_programs_executed':0,'finite_numerical_diagnostics':0,'no_universal_certification_by_evidence':True})
immutable=[bind(p,role) for p,role in sorted(refs.items())];assert all('i158' not in r['path'].lower() for r in immutable);dump(S/'immutable.json',immutable)
print(json.dumps({'focused_immutable_files':len(immutable),'complete_source_files':len(deps),'task_fields':sum(len(x['fields']) for x in context),'embedded_originals':len(occ),'status':'PREPARED; not sealed'},indent=2))
