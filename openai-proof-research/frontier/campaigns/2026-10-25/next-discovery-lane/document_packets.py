import json,pathlib,hashlib,datetime,math,shutil
base=pathlib.Path(__file__).parent
meta={
 'coefficient-positivity':{
  'id':372794,
  'result':'For every natural r and every pair of natural exponents i,j, the coefficient of t^i a^j in the exact Fill--Janson polynomial h(t,a;r) is nonnegative.',
  'proof':'Write x=1+at and A=(x+3t)(x+2t), B=(x+t)(x+4t), C=(x+t)(x+2t), D=x(x+3t), K=8t^4(x+2t). The homogeneous expression H_n=(x+2t)A^n-(x+4t)B^n+(x+2t)C^n-xD^n has auxiliary sequences U_n=H_(n+1)-DH_n and V_n=U_(n+1)-CU_n. Initial values H_0=U_0=0,V_0=K and recurrence V_(n+1)=BV_n+KA^(n+1), together with H_(n+1)=DH_n+U_n and U_(n+1)=CU_n+V_n, prove simultaneous coefficientwise positivity by induction. The source substitution is proved algebraically in Lean.',
  'module':'CoefficientPositivity','main':'all_coefficients_nonnegative',
  'covered':['Every natural r, including 0; not a finite experiment.','Every finitely supported exponent vector on Fin 2, which means every pair of coefficient indices.','Nonnegative coefficient closure under addition, multiplication, and powers.','All initial values and every successor recurrence are ring identities.','sourcePolynomial is written exactly as source (E.16), with t=X 0 and a=X 1.','source_bridge proves equality with the homogeneous expression after substitution.'],
  'novelty':'The MathDB record contains an earlier proof by Shivam Patel (2026-08-20, solution UUID 46acd5c9-9ae6-4584-a626-588caaf59c7b). It uses a positive rational generating function. A live search also found Machina Mathematica / Korea Superintelligence Labs, “Swap differences of powers”, https://ideosphere.ai/papers/fill-janson-coeff, with a 2026-09-07 snapshot and an already reported Lean proof of this exact conjecture. No mathematical novelty, first-proof, or first-formalization claim is made. This packet is a fresh local implementation of a known result, through a triangular recurrence. The external dossier was used for novelty assessment and is not imported into the Lean proof.',
  'source':'Fill and Janson, arXiv:2601.19323v1, Appendix E, Lemma E.8(a), (E.16), Conjecture E.9 (PDF printed page 38).',
  'limits':'This resolves the integer-exponent coefficient question in full. It does not formalize the separate real-exponent probability or root conjectures in the source paper.'},
 'ova-count':{
  'id':350342,
  'result':'There exist prime inputs p=677 and q=401 for which the source construction yields at least 38 distinct prime outputs, disproving both N≤10 and N≤13.',
  'proof':'The input residues are 317 and 41, and both frequencies equal 1. Thus the two primality conditions become Prime(360-r) and Prime(720+r). Thirty-eight explicit residues satisfy the bounds and both primality conditions. Their output values 720+r are distinct. Each output prime itself witnesses that r is a prime residue class modulo 360. Finset inclusion and injectivity prove at least 38 distinct outputs.',
  'module':'OvaCount','main':'prime_count_counterexample',
  'covered':['Both numerical inputs are certified prime.','Residue and frequency functions are defined by actual natural modulo and quotient, not abstract parameters.','Every one of the 38 witnesses meets all numerical source conditions.','Natural subtraction is protected by the explicit r≤residue(p)+residue(q)+2 condition.','The original prime-residue-class condition is bridged with an explicit output-prime witness.','The decomposition into two primes is proved for arbitrary admissible input data.','The counted finite set is the set of distinct output prime values, not merely a list with possible duplicates.','Main theorem provides prime input witnesses, cardinality lower bound 38, and failure of both upper bounds.'],
  'novelty':'The input pair and all 38 residues are from Shivam Patel’s MathDB response dated 2026-08-20 (UUID cb893380-2a3c-48d8-92d6-21c99c7f1ce8). This is a formal verification of that known posted counterexample, not a new discovery. A targeted exact-phrase search did not add a different earlier source, but this is not proof of literature priority.',
  'source':'MathDB 350342 states N≤10 and points to arXiv:2104.04522. The retrieved arXiv v1/v2 use the construction while citing Theorem 7 of the 2020 Revista Politécnica paper, DOI 10.33571/rpolitec.v16n32a10. That original paper’s Conjecture 1 (printed p.117) states N≤13. The source mismatch is explicitly recorded, and the same witness refutes both.',
  'limits':'The theorem proves a lower bound of 38, which fully refutes the conjecture. It does not assert that 38 is the exhaustive total, despite that claim in the prior post. It does not use or verify the source’s general existence theorem, nor any Goldbach claim.'}}
for slug,m in meta.items():
 p=base/slug; audit=json.load(open(p/'build/audit.json'))
 (p/'README.md').write_text(f'''# MathDB {m['id']}: ready for parent review

**Full outcome:** {m['result']}

**Status:** the complete Lean module passes the pinned verifier. Independent parent review is pending, so this lane has not counted or released it as accepted.

## Source

{m['source']}

The exact fetched post, including all posted solutions, is in `source.json`; raw response and original papers are archived in `../sources/`. `primary-reference.json` records hashes and the credited reply.

## Proof

{m['proof']}

## Deliverables

- `main.tex`: detailed manuscript; `build/main.pdf`: built paper.
- `formal/{m['module']}.lean`: complete single-module proof.
- `formal/Checks.lean`: declaration and axiom checks, copied from the pinned verifier.
- `build/audit.json`: compiler receipt; `build/Checks.log`: full declaration/axiom output.
- `coverage.json`, `NOVELTY.md`, `self-review.md`: scope and review notes.

Run from the campaign directory:

```sh
python ../twenty-proof-campaign/verify_outcome.py {slug}
```

The verifier uses Lean 4.34.1 and the already installed package revisions in `pins.json`. The canonical main theorem is `{m['module']}.{m['main']}`. Its module has {audit['declarations']} audited declarations. No omitted proof placeholders or non-kernel computation are present.

## Limits

{m['limits']}

{m['novelty']}
''')
 (p/'PROOF.md').write_text(f'# Full proof outline\n\n{m["result"]}\n\n{m["proof"]}\n\nAll algebra, finite membership tests, and source bridges are proved in the module. See `main.tex` for the detailed argument.\n')
 (p/'NOVELTY.md').write_text('# Provenance and novelty review\n\n'+m['source']+'\n\n'+m['novelty']+'\n\nThe search was bounded, not an exhaustive literature review. The justified status is a formal verification of an already posted result, not discovery. This question is distinct from all exclusions supplied in the task.\n')
 (p/'coverage.json').write_text(json.dumps({'source_id':m['id'],'claim':m['result'],'full_outcome':True,'covered':m['covered'],'unproved_bridges':[],'scope_limits':m['limits'],'review_status':'self-checked; independent parent review pending'},indent=2)+'\n')
 (p/'self-review.md').write_text('# Self-review (not independent review)\n\n'+ '\n'.join('- '+x for x in m['covered'])+'\n\nThe original statement and formula were checked against the fetched primary PDF. The main theorem is a full proof/disproof of the indicated MathDB problem, not a supporting lemma or finite test of a universal positive claim. The proof is independent of unverified posted assertions. All definitions, helper lemmas, and final theorem passed the canonical build and axiom audit.\n\n'+m['limits']+'\n\nIndependent source-fidelity and proof review is reserved for the parent. No accepted-count or review hash has been written.\n')
 shutil.copyfile(p/'build/Checks.lean',p/'formal/Checks.lean')
 (p/'verification.json').write_text(json.dumps({'lean':audit,'independent_review':'pending parent','full_scope_claim':m['result']},indent=2)+'\n')
# Independent arithmetic inventory (supplementary, not the proof certificate).
rs=[7,13,23,49,53,67,77,89,91,103,109,119,133,137,161,163,167,187,209,221,233,247,251,257,263,271,277,289,293,299,301,313,319,329,331,341,343,349]
def prime(n):return n>=2 and all(n%d for d in range(2,math.isqrt(n)+1))
assert len(set(rs))==38 and prime(677) and prime(401)
assert all(0<r<360 and prime(360-r) and prime(720+r) for r in rs)
(base/'ova-count/witnesses.json').write_text(json.dumps([{'r':r,'complement':360-r,'output':720+r} for r in rs],indent=2)+'\n')
(base/'README.md').write_text('''# Next discovery lane: two complete candidates

This lane produced two distinct full MathDB outcomes, ready for independent parent review:

| ID | Full outcome | Lean result |
|---|---|---|
| 372794 | Every coefficient of the Fill–Janson polynomial is nonnegative for every natural exponent | `CoefficientPositivity.all_coefficients_nonnegative` |
| 350342 | Inputs 677 and 401 produce at least 38 distinct prime outputs, refuting both the MathDB bound 10 and original bound 13 | `OvaCount.prime_count_counterexample` |

Both are honest verifications of earlier posted results, not new-discovery claims. Each directory contains the full single-module Lean proof, source record with solution credits, detailed paper, scope/novelty notes, and pinned build receipts. Both main proofs pass Lean 4.34.1 and the canonical forbidden-token/axiom audit. Independent review is pending. No git, shared index, or accepted ledger was modified.

## Important source facts

- MathDB 372794 has a prior proof by Shivam Patel and an existing public Lean dossier by Machina Mathematica / Korea Superintelligence Labs. The local proof uses a compact triangular recurrence and fully proves the source-formula identity.
- MathDB 350342 states the bound 10. Its linked 2021 arXiv source refers to the construction in a 2020 publication whose Conjecture 1 actually states 13. Both are refuted. The local theorem certifies **at least 38**, not an exhaustive equality.

## Next action for parent

Review `coefficient-positivity/main.tex` with `formal/CoefficientPositivity.lean`, and `ova-count/main.tex` with `formal/OvaCount.lean`. The exact fetched MathDB records and source PDFs are under `sources/`; hash inventories are in each `primary-reference.json`. If accepted, integrate each as one outcome; supporting closure/recurrence/count lemmas are not separate outcomes.
''')
(base/'search-notes.md').write_text('''# Search record

Read all four requested queued lists and the project AGENTS.md and pinned upstream metadata. Fetched 27 exact posts into `sources/`, preserving their posted solutions. Four additional fetches encountered rate limiting and were not treated as evidence. No queued/shared source file was changed.

Selected two full outcomes after inspecting the exact post statements and primary source PDFs. The polynomial result has a known positive generating function that admits a compact division-free recurrence. The Ova claim has a small certified finite counterexample. Both are distinct from the excluded/assigned IDs.

Other fetched candidates were not claimed: 378626 requires substantial coprimality theory despite a posted solution; 405260 concerns multivariate formal power series; 371791, 371324, 374660–374666, 337932, 343909, 358561, 370181, and 327048 require additional structural work; 364540, 352508, 338823, 338822, 349070, 344947–344949, and 382158 were inspected but not selected. They have no proof outcome in this lane.

A targeted public search found the prior Fill–Janson formalization at https://ideosphere.ai/papers/fill-janson-coeff (snapshot 2026-09-07). This is explicitly credited; no novelty is inferred from search absence for other claims.
''')
