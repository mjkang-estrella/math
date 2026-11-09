from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent
r=json.loads((L/'fresh-replay/replay-receipt.json').read_text())
bindings=json.loads((L/'input-bindings.json').read_text())
pdf=next(x for x in bindings if x['path'].endswith('/primary/ajc_v94_p267.pdf'))
prov={'primary':dict(pdf,url='https://ajc.maths.uq.edu.au/pdf/94/ajc_v94_p267.pdf',citation='Cerbai–Claesson–Ernst–Golab, Pattern-avoiding Cayley permutations via combinatorial species, AJC 94(2) (2026), 267–299',definition_page=280,conjecture_page=296),
 'source_review':'Published PDF read locally after binding, including initial-interval definition, strict-index definition, Section 8 end, Proposition 8.4 proof body and conjectures 8.5–8.8. Extracts retained. No external request in this lane.',
 'review_intake':'../root-mathdb-cayley-review-intake-r336/corrected-record.json and DECISION.md; its retained independent review and checker were read after binding.',
 'predecessor':'../pi-cayley-avoidance-source-formal-r337; partial files bound before content and retained untouched in place. Its code is unfinished and was not adopted as a certificate.',
 'implementation_reuse':'Pinned compiler, package checker, serial Lean guard and exhaustive audit scaffolding adapted from bound sol-das-ap-irreducible-source-formal-r1. New mathematical definitions/proofs independently written in this lane. Existing independent Cayley checker functions re-used read-only for a separate computational cross-check.',
 'prior_art':'Inherited bounded review only. Named successor coverage is not fully retained primary-body evidence; no new literature-wide clearance, current public-registry clearance, or successor-body completeness claim. Novelty HOLD.',
 'network':{'requests':0,'MathDB':'429 HOLD, zero requests','prohibited_routes_used':False},
 'integrity':'input-bindings.json contains flat original SHA256+size references, not a copied history corpus; final_verify.py rechecks these originals.'}
(L/'source-provenance.json').write_text(json.dumps(prov,indent=2,ensure_ascii=False)+'\n')
d={'mathdb_id':364119,'source':'AJC 94(2) (2026), Conjecture 8.8 p.296, strict-index definition p.280',
 'disposition':'FORMAL_REFUTATION_COMPLETE_ACCEPTANCE_HOLD','formal_status':'PASS_UNCONDITIONAL_LITERAL_SOURCE_NEGATION',
 'endpoint':'Cayley.literal_source_claim_false : ¬ Cayley.SourceClaim',
 'witness':{'p':[1,1,2,2],'q':[1,1,1,2],'n':5,'max_p':2,'max_q':2,'total':541,'avoid_p':520,'avoid_q':522,'contain_p':21,'contain_q':19},
 'finite_universe_bridge':'Generic maxL_le_length, mem_allWords, nodup_allWords, mem_wordUniverse, wordUniverseEquiv, mem_avoiders, avoiderEquiv, sourceCount_eq; no assumed finite Nat-function universe.',
 'replay':{'directory':'fresh-replay','declarations':r['actual_declaration_count'],'generated_partial_declarations':[],'axioms_allowed':['propext','Classical.choice','Quot.sound'],'archive':'source-only.tar.gz'},
 'evidence':{'statement':'published PDF retained and bound','primary_body':'published definitions and closest internal proof body read','prior_art':'bounded inherited evidence with primary successor-body gaps; HOLD','mathematical':'exact independent n5 computation plus kernel-checked counts','formal':'safe source-only serial replay and exhaustive declarations/transitive-axiom audit PASS'},
 'novelty':'HOLD','acceptance':'HOLD','accepted_credit':0,'counts':{'additional':9,'total':39,'next':40},
 'process_exceptions':'failures/procedural-deviations.json; initial unguarded binding helper and temporary scripts outside lane, since moved here; no predecessor/shared edits.',
 'remaining':['Independent adversarial formal review','Root extracted replay and source-scope adoption','Stronger retained successor primary-proof-body and current public-registry prior-art coverage when access permits','Root acceptance adjudication','Any manuscript/PDF gates only if separately authorized; no manuscript investment here']}
(L/'disposition.json').write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
(L/'SUMMARY.md').write_text('''# MathDB 364119 — literal formal refutation complete; acceptance HOLD

The final endpoint is `Cayley.literal_source_claim_false : ¬ Cayley.SourceClaim` in `Witness.lean`. It refutes the full generic published Conjecture 8.8, not a conditional counting helper. The witness is p=1122, q=1112, n=5, equal length four and maximum two. The kernel proves 541 Cayley words, 520 avoiding p and 522 avoiding q, with complementary containment counts 21 and 19.

`Definitions.lean` defines positive Nat-valued lists whose letter set is an initial interval. `Contains` requires an order-isomorphic sublist; `strict_indices` proves equivalence to extraction by an order embedding of finite position sets, hence strictly increasing distinct positions, preserving strict comparisons and equalities for each earlier/later pair. The authoritative definition is the published AJC PDF p.280; the conjecture and same-length scope occur on pp.295–296. The arXiv index typo is not used.

The finite alphabet is proved complete for every length: `maxL_le_length` bounds every packed word, `mem_allWords` characterizes the enumeration, `nodup_allWords` rules out duplicates, and `wordUniverseEquiv` supplies an actual generic bijection to all Nat-valued source words. `avoiderEquiv` and `sourceCount_eq` identify the enumerated count with the cardinality of the literal source subtype. No finite universe of arbitrary Nat-valued functions is assumed. Empty words are treated consistently as positive-letter initial-interval words with maximum zero.

Fresh source-only serial replay passed in `fresh-replay/`. The compiler hash and all nine package pins passed before and after. All 87 declarations, including compiler-generated declarations, have full types and transitive axiom reports in `fresh-replay/Audit.log`; the allowed axiom set is exactly restricted to propext, Classical.choice and Quot.sound. There are no generated partial declarations. The count proofs use ordinary kernel `decide`, with no native evaluation shortcut. `source-only.tar.gz` is deterministic and contains only own source/configuration/utilities, with no compiled objects or third-party library copies. Own compiled outputs are removed after successful audit; logs and receipts remain.

The separate computational cross-check uses the bound independent review functions read-only and checks both pairwise comparison and rank-normalization on every one of the 541 words; the source-known 112/122 control at n=5 also passes. See `independent-check.json`. This is mathematical cross-check evidence, distinct from the kernel certificate.

Failures are preserved under `failures/`, including RSS-cap terminations and the audit that rejected an initial compiler-generated partial recursion helper. The final enumeration uses explicit `Nat.rec`. No resource limits were raised. Python helper work uses the specified 512 MiB AS/groupRSS, CPU210, wall230 guard; Lean uses the separately authorized pinned serial guard from the reference RUN.md (RSS2800 MiB, CPU210, wall230). Initial procedural exceptions are recorded candidly in `failures/procedural-deviations.json`: an unguarded initial binding command, temporary creation scripts first written outside the lane and subsequently moved here, a bad relative pin invocation, and a stale early audit. Final acceptance evidence uses only the fresh serial replay.

No network requests were made. MathDB remains on 429 HOLD. Source provenance uses flat in-place SHA256+size references; originals are reverified by the final verifier. The cancelled Pi predecessor remains untouched; its unfinished proof sketch is not evidence of completion. The bound primary PDF and independent reviewer/checker, rather than defective old controls or unscoped sweeps, supply intake evidence. No broad new-literature or live-registry clearance is claimed. Published source and formal evidence are distinguished from the incomplete retained successor-body prior-art evidence.

## Reproduce

Extract `source-only.tar.gz` into a new directory inside this lane and run `bash run.sh`. The runner checks pins, compiles Definitions then Witness serially, audits every declaration, checks allowed transitive axioms and source hashes, then rechecks pins. It uses the existing pinned library in place and does not access the network. Run all Python utilities with OPENBLAS_NUM_THREADS=1, OMP_NUM_THREADS=1, PYTHONDONTWRITEBYTECODE=1 and `python3 -B` through the specified helper guard. After the final manifest is written, run that guard on `python3 -B final_verify.py`; it exits nonzero on inventory, SHA256, size, original binding, archive, or replay mismatches.

## Completed scope and remaining obligations

Completed: unconditional literal source refutation, generic finite-alphabet bound and bijections, exact counts, source binding/provenance, independent computational cross-check, deterministic source-only archive, fresh serial replay, exhaustive declaration/transitive-axiom audit, preserved failures, exact manifest and separate final verifier. The only final-manifest exclusions are `manifest.json` itself and the named `verification-receipt.json`.

Remaining: independent adversarial formal review; root replay and source-scope adoption; stronger retained successor proof-body/current-registry prior-art coverage when permitted; root acceptance adjudication; any separately authorized manuscript/PDF gates. Novelty and acceptance remain HOLD. No manuscript was written. Credit is zero; counts remain **9 additional / 39 total / next 40**. No shared files, predecessors, ledgers, git, or public services were changed.
''')
# Remove only this lane's own compiled outputs, including failed own replays.
removed=[]
for p in L.rglob('*.olean'):
 b=p.read_bytes();removed.append({'path':str(p.relative_to(L)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)});p.unlink()
(L/'compiled-output-cleanup.json').write_text(json.dumps(removed,indent=2)+'\n')
# Keep stale top-level reports clearly separate from successful extracted replay.
for n in ['Definitions.log','Definitions.guard.json','Witness.log','Witness.guard.json','Audit.log','Audit.guard.json']:
 p=L/n
 if p.exists():p.rename(L/'failures'/('pre-final-'+n))
files={}
for p in sorted(L.rglob('*')):
 if p.is_file() and str(p.relative_to(L)) not in ['manifest.json','verification-receipt.json']:
  b=p.read_bytes();files[str(p.relative_to(L))]={'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
(L/'manifest.json').write_text(json.dumps({'algorithm':'SHA256','exclusions':['manifest.json','verification-receipt.json'],'files':files},indent=2)+'\n')
print('manifest files',len(files),'declarations',r['actual_declaration_count'])
