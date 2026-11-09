import pathlib,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parents[1];X=json.loads((D/'extracted.json').read_text())
notes={
'58':('open_partial','Primary Theorem1.1 proves Sperner<=socle+1 only. Binary-coefficient ternary cubic Hessian search is a known-degree diagnostic, not remaining odd compressed regime. Need degree>=7 construction or full WLP proof.'),
'315895':('known_resolution_lead','Classical character formula proved by Beilinson-Bernstein and Brylinski-Kashiwara. Search surfaced primary 1981 and Vogan accounts; original theorem/proof bodies not audited here. Do not exploit sign or indexing conventions.'),
'315907':('public_full_proof_claim','Source proves dimension4. Later2610.10545 Theorem1.2 states exact all-n>=2 inequality and uniqueness, with boundary proof Sections5,6. Theorem and proof roadmap read, full proof not independently verified. No novelty clearance.'),
'315995':('open_small_order_gap','Classical asymptotic1-factorization theorem does not cover every finite order. All labeled graphs through6 checked. Need finite gap or genuinely new full proof; no claim asymptotic result settles literal universal.'),
'315999':('open_partial','All labeled trees orders2..6 have graceful labeling by exhaustive Prufer/bijection test. This is far below known computations and supplies no discovery.'),
'316020':('open_partial','All labeled graphs orders1..6 tested; every minimum-degree3 graph contains4-cycle. Need substantially new construction or structural theorem, no small counterexample.'),
'316022':('open_partial','All4-connected labeled graphs orders5..6 Hamiltonian, without needing toroidal filter. Exact torus embedding not implemented beyond that superfamily test.'),
'316026':('open_partial','Primary1010.4430 is a large-tournament theorem, not all-n resolution. Exhausted tournaments2,4 against oriented trees2,3. n1 empty-tournament endpoint is excluded correction.'),
'316037':('open_partial','All loopless simple digraphs orders2..4, including opposite arcs, satisfy exact dicut-color test. k0/1 are trivial. No general dijoin-packing proof.'),
'316059':('open_no_finite_decider','Infinite additive-basis eventual-positivity and unbounded-limsup statement; bounded subsets cannot certify a counterexample. No full proof mechanism obtained.'),
'316062':('open_partial','Exact positive-integer equal-power search for k3..8 entries<=15, each side length<=3 and m+n<k, no common term; no witness. Does not test arbitrary side lengths.'),
'316164':('known_resolution_lead','Marcus-Tardos2004 theorem and Klazar reduction are known full-scope leads; primary proof body not retrieved here. New Lean formalization alone cannot earn novelty credit.'),
'318034':('open_partial_source','Primary0812.2750 retrieved. Limiting moments and burn-size law require stochastic asymptotics. Later coalescent-with-deletion literature surfaced but not full-scope compared; no resolution clearance.'),
'326053':('open_partial_source','Primary1308.0779 retrieved; partial Frobenius/Grothendieck-group equality includes specified character, inertia and Tate actions. No complete semantic reconstruction or later-resolution screen.'),
'331759':('open_sustained_partial','Read actual definitions, Conjecture, Theorems1,2 and downset/polytope proof route. Exact small-family search and capped n4,s4 extension found no counterexample. Need general compression/classification beyond Theorem2 assumptions.'),
'340094':('open_sustained_partial','Read Conjecture1.1, Theorems3.6,3.8 and Remark3.2. Four statistics known, inverse/NE-transpose condition expressly not proved. Exhaustive refined fixed-point distributions through6 match; extended7 separately logged. Need uniform refined involution enumeration or counterexample.'),
'344690':('open_partial_source','Primary retrieved; successive maxima conjecture has density/probability-one qualification and excludes wild-ramification issue. No fully fixed probability semantics or numerical field database search; not clearance.'),
'356967':('open_partial_source','Current primary proves zig-zag in smoothly varying families, with exceptional weights/slopes constraints. No full-scope bridge for every literal parameter established; do not count family theorem as universal.'),
'358976':('open_partial_source','Primary Conjecture0.3 read in context. NLE, unbounded Woodin/strong cardinals, collapse and Chang model properties remain deep inner-model assumptions. No finite counterexample test applies.'),
'360929':('open_partial_source','Primary Conjecture15 and exponential-jump restriction inspected. General jump distribution extension needs existence, uniqueness, speed selection and stationary convergence. Later2025 publication still conjectures general extension in search excerpt; full journal proof body unread.'),
'368329':('open_partial_source','Primary retrieved; extraspecial nonconstrained fusion-system cases verified in source. Global seven assertions not subsumed by those cases. Compatible-family invariants not implemented; finite-group search missing.'),
'371188':('source_scope_gap','Primary NLS setup restricts numerical work to1,2 dimensions. Raw all-dimensional blow-up/stability wording requires precise source conjecture and scaling comparison before any refutation. No correction earns credit.'),
'372281':('already_refuted_primary','Actual Lemma4.2 and its proof parameterize diagonal channels and provide exact rational2D optimal solution failing spectral sign condition. This is the source authors own counterexample, not new.'),
'374765':('open_partial_source','Primary retrieved; sufficiently-large-n quantifier means finite exceptional n cannot refute claim. Expansion definition and asymptotic family construction not implemented; finite graph search missing for this ID.'),
'379197':('open_partial_source','Primary retrieved; hat-J normalization and uniform n near N/2 asymptotic cannot be replaced by finite knot evaluations. No later full-scope resolution comparison completed.'),
'379350':('open_partial_source','Primary Conjecture1.2 and known surfaces/products/Kodaira-Thurston cases inspected. Universal closed symplectic-manifold equality is not proved by those cases.'),
'379351':('open_partial_source','Same primary distinguishes metric-extension obstruction from stronger bounded-isometry conjecture. No universal result or full literal noncompact scope bridge obtained.'),
'380306':('open_partial_source','Primary v3 retrieved; p2 factorization known, p3,p5 conjectured. Need exact overconvergent-space weight/radius and U-matrix definitions; no determinant/valuation search implemented.'),
'380929':('routine_corollary_excluded','Actual Conjecture1 identity is coefficient extraction from exp(lambda*C(t))*exp(mu*C(t))=exp((lambda+mu)*C(t)), C=sum c_j t^j. Explicit finite multinomial proof in ROUTES.md. Symbolic k0..10 checks, no significance claim.'),
'380939':('open_partial_source','Primary AppendixB ConjectureB.1 read: Jacobi-integrable homogeneous Newton systems, all higher variational equations at Darboux phase curve. Hamiltonian Morales-Ramis-Simo theorem alone is not a source bridge.'),
'381131':('partial_known_and_formulation_defect','Later1506.06238 Lemma1 states exact stabilization time i+j+1. Literal staircase >=3k already conflicts with authors k1 table coefficient alpha3,0,1=1/3; endpoint correction excluded. Recurrence script fails later table consistency and is quarantined, not a valid refutation of intended staircase.'),
'381556':('open_partial_source','Primary iterated extension conjecture retrieved. lc-centre filtration, orthogonal norms and uniform normalization not fully reconstructed; no short proof or finite search applies.'),
'381659':('routine_existence_bridge','Source Conjecture5 preceded by generating-function identity C_sp,ap(0,1,x)=1+x F_E(x). Coefficient equality of finite sets already gives existence via rank ordering; requested direct combinatorial mapping may remain interesting. Enumeration n1..9 agrees; no new credit.'),
'382052':('open_partial_source','Actual Conjecture6.4.4 inspected. Need motivic-to-numerical self-dual invariant definitions, not merely generalized binomial recurrence. No invariant computation implemented.'),
'382460':('open_partial_source','Actual Conjecture6.2 extends crystallographic Theorem6.1; noncrystallographic Deodhar word statistics/fake degrees require full implementation. No small Coxeter search implemented.'),
'382565':('source_semantic_gap','Definition3.2 requires irreducible reduced curves in general-point linear systems satisfying delta^2-2sum mu^2=-3 and sum mu=2delta. Integer data alone is insufficient; source explicitly gives nonrealizable examples. No geometric witness or full proof.'),
'394120':('known_resolution_lead','Literal is Lisca lens-space/rational-ball/ribbon classification. Primary report page fetched and Lisca math/0701610 lead found. Original proof not audited here; no novelty investment justified.'),
'399483':('open_partial_source','EMS report page retrieved, but full underlying discrete uniformization statement/metric convergence topology not reconstructed. No exact finite decider for epsilon->0 convergence.'),
'399559':('open_partial_source','EMS report and1503.00921 fetched. Graded Laurent-ring equivalence is stronger than known v1 integral KOR theorem; do not collapse specialization to graded conjecture. No Cartan computation implemented.'),
'400138':('open_sustained_partial','Primary1507.04080 Conjecture1.2, Theorem1.4 and all-lines lower-bound context inspected. Raw i=2q-1 numerator has opposite signs to primary; correction excluded. Exact all subsets PG(2,2),PG(2,3) minima agree with published small-d table. Need all-field gap bound for intended remaining range.')}
searches={}
for f in (D/'outputs').glob('search-*.json'):
 o=json.loads(f.read_text());ids=o.get('ids',[o.get('id')]);
 for i in ids:
  if i is not None:searches.setdefault(str(i),[]).append(str(f.relative_to(D)))
out={}
for i,o in X.items():
 status,note=notes[i];src=D/f'sources/{i}.html';files=[str(src.relative_to(D))] if src.exists() else []
 files += [str(f.relative_to(D)) for f in (D/'sources').glob(i+'-*.html')]
 out[i]={**o,'outcome':status,'accepted_credit':0,'review_depth':'literal raw extraction; selected primary passages only' if files else 'literal raw statement and bounded leads; primary body not read','primary_files':files,'finding':note,'search_coverage_files':searches.get(i,[]),'finite_search_status':'diagnostic recorded; consult exact space and limitations' if i in searches else 'not implemented or not applicable; no exhaustive-coverage claim','history':'history-exact-matches.txt: bounded conclusion filenames; only current reservation ledger hit found, not a global nonreview proof','registry':'live heads plus complete Omega D5/Problems path screens, not proof-body clearance','lean_endpoint':None,'remaining_acceptance_gates':['source fidelity completion','bounded later-literature and author-catalogue comparison','significant rigorous full-scope proof','literal Lean endpoint and all semantic bridges','strict fresh replay, leanchecker and full declaration axiom audit','independent root acceptance']}
assert len(out)==40 and set(map(int,out))==set(json.loads((D/'reservation.json').read_text())['ids'])
(D/'results.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
receipts=[]
for f in (D/'sources').glob('*.receipt.json'):receipts.append(json.loads(f.read_text()))
(D/'outputs/receipts-index.json').write_text(json.dumps(receipts,indent=2)+'\n')
(D/'outputs/artifact-hashes.json').write_text(json.dumps({str(f.relative_to(D)):hashlib.sha256(f.read_bytes()).hexdigest() for f in D.rglob('*') if f.is_file() and f.name!='artifact-hashes.json'},indent=2)+'\n')
print('40 entries, credit0; no Lean claim')
