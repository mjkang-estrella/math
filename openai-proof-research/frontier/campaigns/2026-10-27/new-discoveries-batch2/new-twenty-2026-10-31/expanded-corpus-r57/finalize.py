from pathlib import Path
import hashlib,json,datetime
p=Path(__file__).resolve().parent;records=json.loads((p/'records.json').read_text());prov={str(x['id']):x for x in json.loads((p/'provenance.json').read_text())};sources={'362436':'2403.16197','362542':'2403.20304','362895':'2404.18806','362836':'2404.15167','362468':'2403.17568','362525':'2403.19737','362322':'2403.09943'}
notes={
'362277':'Polynomial algorithm requires structural longest-path decomposition and bit-complexity proof; no constructive mechanism derived.',
'362314':'Function-field ring, ideal representation and input complexity are source-dependent and remain unrecovered; no HNF endpoint.',
'362338':'Topological subdivision of every orientation under both semidegree bounds; no full-scope construction.',
'362339':'Tightness does not imply a unique limiting random shift; extremal process and derivative-martingale mechanisms unproved.',
'362369':'Need uniform control over every edge-colouring and asymptotic tree-cover threshold; no finite witness suffices.',
'362381':'Partition admission predicates absent from literal; source notes counterexamples but their actual scope is unread.',
'362384':'Uniform additive constant and identifiable graph classes require primary hypotheses; no new mechanism.',
'362392':'Literal finite-n function versus limiting exponent is ambiguous; source asymptotic formulation must be recovered, not corrected for credit.',
'362397':'Figure 1 axioms not in literal; completeness cannot be investigated from the paraphrase alone.',
'362440':'Needs girth≥5 cubic graph with certified absence of total 4-colourings or all-graph proof; no such candidate generated.',
'362467':'Distribution P_n and uniformity assumptions unrecovered; arbitrary cluster distributions would widen source scope.',
'362507':'Twist invariant e and ruled-surface normalization not recovered from primary body; no source-faithful witness.',
'362534':'Algebra extension and indecomposable summand construction source-dependent; no semantic endpoint.',
'362582':'Transfer normalizations and regular-semisimple matching source-dependent; no feasible full-scope Lean route.',
'362612':'Adversarial colouring quantifier and depth convention need primary verification; no random tournament proof.',
'362648':'Raw text already flags multigraph counterexample; source simple-graph scope takes precedence. No paraphrase correction claimed.',
'362649':'Duplicate source family of 362648, not a separate candidate for credit; influence matrix definitions unread.',
'362682':'Quantifier order for jet bound may differ from standard ideal-adic conjecture; primary body required before any objection.',
'362691':'Eventual threshold deliberately excludes small witnesses; need counterexamples beyond 4k²+2k or full bound.',
'362705':'Existential universal indegree threshold requires unbounded family, not finite low-degree counterexample.',
'362792':'Logical circuit and non-trivial Pauli angle semantics source-dependent; Clifford generation alone is not a bridge.',
'362810':'All-n topological crossing lower bound remains far beyond mechanisms developed here; no claim of current literature status.',
'362811':'Complete bipartite crossing-number family likewise lacks a new full-scope mechanism.',
'362873':'Integrality/divisibility of n+1 by 3 needs source check; rounding endpoint corrections excluded.',
'363029':'PSPACE upper bound from finite play is insufficient; needs reduction proving full lower bound.',
'363036':'Literal credits Lovasz; known-result lead only in this pass, original primary proof not read; no rediscovery.',
'363067':'Almost all and exceptions not formally specified; no precise primary endpoint recovered.',
'363117':'Energy functional minmin1 not supplied in literal; no source-faithful minimizer proof possible yet.',
'363168':'Normalization and extremal direction of Delta prime not recovered; area construction without these is not a solution.',
'363258':'Formal uncertainty and duality predicates not defined in literal; no source semantics recovered.',
'363284':'Raw open-twin-free definition omits closed twins and isolation conventions; no wording counterexample credited.',
'363286':'Asymptotic family hypothesis and fixed forbidden induced length require primary verification; no full mechanism.',
'363317':'No-lonely-colour condition is stronger than popular-colour condition; no implication or bounded chromatic construction proved.'}
out={}
for i,d in records.items():
 row=dict(mathdb_id=int(i),title=d['title'],literal_statement=d['statement'],canonical_url=d['canonical_url'],provenance=prov[i],inherited_matches=[{'kind':'current assignment only','path':'../ledger.json initial_targets of expanded-corpus-r57'}],historical_screen='history-exact-id-paths.json and history-title-paths.json; no prior technical disposition located in checked report scopes; absence not global nonreview',review_depth=dict(literal_read=True,source_definitions_read=False,source_claim_body_read=False,proof_body_read=False,inherited_primary_review_reused=False),outcome='HOLD_PRIMARY_UNREAD_NO_ENDPOINT',reason=notes.get(i,''),new_credit=0,accepted_credit=0,lean_endpoint=None,source_receipts=[],remaining_lemmas=[],mathematical_attempts='ATTEMPTS.md')
 if i in sources:
  a=sources[i];row['source_receipts']=[json.loads((p/'sources'/(a+'.receipt.json')).read_text())];row['review_depth'].update(source_definitions_read=True,source_claim_body_read=True,proof_body_read=True)
  row['review_depth']['scope']='Selected sections only, detailed in ATTEMPTS.md; not whole-paper proof verification.'
 if i=='362436':row.update(outcome='ORDINARY_COUNTEREXAMPLE_HOLD_FORMAL_AND_QUALIFICATION',rank=1,reason='C_12 categorical K_4, 48 vertices, all distances preserved by every vertex deletion, none surrounded, diameter 6 > floor(log2 48)=5.',ordinary_proof='ORDINARY-PROOF.md',formal_partial='Generic.lean',formal_attempt='Candidate.lean',remaining_lemmas=['finite distance certificate properties','induced-deletion distance equality','no surrounded vertices','connectedness','antipodal distance and logarithm comparison','literal negation endpoint'],qualification='No independent review or published/direct-product prior-art clearance. Zero credit.')
 if i=='362542':row.update(outcome='PARKED_UNIFORM_PRIME_EXISTENCE_AND_MINIMALITY_GAP',rank=2,reason='Primary Section 4 lower bounds known; bounded ordered search finds no refutation. Zero forbidden in primary penholodigital definition.',remaining_lemmas=['uniform prime in earliest admissible numerical word window','minimality for every base','exact digit/primality Lean semantics'])
 if i=='362895':row.update(outcome='PARKED_SUBSTANTIVE_CASE_UPPER_BOUND_GAP_ENDPOINT_EXCLUDED',rank=3,reason='Source lower construction read; row transfers agree for eligible heights≤30 and odd widths 3,5,7. Width 1 failures are excluded domain endpoints.',remaining_lemmas=['uniform upper bound for genuine two-dimensional boards','soundness of any transfer certificate in Lean'])
 if i in ['362836','362468','362525']:row.update(outcome='EXCLUDE_SAME_SOURCE_KNOWN_RESULT',reason={'362836':'Section 6 explicitly refutes Conjecture 1.2 using lollipop–bipartite graphs; actual proof read.','362468':'Theorem 4 and Section 2 induction prove the exact minimum-degree≥2 claim.','362525':'Theorem 1.2 and Section 2 epsilon-net / VC-dimension proof prove the exact polynomial claim.'}[i])
 if i=='362322':row.update(outcome='PARKED_SOURCE_PARTIAL_BOUND_ONLY',reason='Definitions, Conjecture 2 and Theorem 6 proof read; partial large-parameter result not a full solution, uniqueness/tie correction not credited.')
 out[i]=row
assert len(out)==40 and set(out)==set(map(str,json.loads((p/'reservation.json').read_text())['ids']))
(p/'results.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
(p/'Candidate-attempt1-transcript.txt').write_text('Preserved from tool output, not an original complete process log. Initial run exit 1 under AS 6 GiB:\nCandidate.lean:1:0: error: failed to read file Mathlib/Data/Finset/Image.olean.private\nThe file was subsequently found present. AS 64 GiB allowed import. Initial run receipt and log were overwritten before archival; this is an explicit retention limitation.\n')
(p/'artifact-manifest.json').write_text(json.dumps({str(f.relative_to(p)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(p.rglob('*')) if f.is_file() and f.name!='artifact-manifest.json'},indent=2)+'\n')
print('Exactly',len(out),'results;',sum(x['review_depth']['source_definitions_read'] for x in out.values()),'selected primary contexts; zero new credit.')
