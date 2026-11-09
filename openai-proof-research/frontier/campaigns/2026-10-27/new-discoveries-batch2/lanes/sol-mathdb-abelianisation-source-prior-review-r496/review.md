# MathDB339564: retire as publicly resolved

Recommendation: RETIRE this screening candidate. No discovery credit or acceptance recommendation. No Lean or manuscript work. Counts remain **9 additional / 39 total / next 40**.

## Scope and literal source

Only MathDB339564 and author brief P2 were scientifically inspected. Mohamed–Williams, *An investigation into the cyclically presented groups with length three positive relators*, arXiv:1806.06821v2, dated 12 August 2019, equation (2), defines

Γ_n(k,l) = <x_0,…,x_{n−1} | x_i x_{i+k} x_{i+l}, 0≤i<n>, with subscripts modulo n.

Here d denotes minimum number of generators (p.9), not torsion-free rank. Conjecture 4.4 (p.12) quantifies over all integers n≥8 with gcd(n,6)=2 and asserts d(Γ_n(1,n/2−1)^ab)=1,2,3 according as gcd(n,16)=2,{4,16},8. Thus n=2m, m≥4, 3∤m. Theorem 4.1 supplies finiteness: condition (A) requires 3|n, impossible here, hence Betti number zero. Corollary 3.11(b) already supplies the lower bound three when gcd(n,16)=8. The source’s GAP range n≤500 and the author’s 52 SNF diagnostics are finite evidence only.

Read: primary definitions (1),(2), condition (A), Section 4 setup, Theorem 4.1 and proof, Theorem 4.2 statement and relevant surrounding text, Corollary 4.3, Conjecture 4.4 and surrounding proven lower bound. No other candidate brief was read.

## Decisive public successor: actual statement and proof

Noferini–Williams, *Smith forms of matrices in Companion Rings, with group theoretic and topological applications*, Linear Algebra and its Applications **708 (2025), 372–404**, DOI 10.1016/j.laa.2024.12.003, Section 4.5, **Theorem 4.10, Lemma 4.11, proof pp.397–401, Corollary 4.12**. The complete publisher PDF was obtained lawfully from Aalto's repository, HTTP 200 on 2026-10-31T12:30:08Z. Body chronology: received 16 August 2024, revised 22 November 2024, accepted 5 December 2024, available online 16 December 2024. Repository cover has the distinct date 01/03/2025. The arXiv search identification 2408.08662 was a lead only: no claim that its first version contains the same theorem has been inferred.

Actual published Corollary 4.12 expressly identifies itself with Mohamed–Williams [30, Conjecture 4.4] and gives the same three values for G_n(x_0 x_1 x_{n/2−1}). Reference [30] identifies the Mohamed–Williams paper, Experimental Mathematics 31(2) (2022), 537–551. This is body evidence, not reliance on title, abstract, metadata, or an open-record label.

Theorem 4.10 is stronger. Put r=gcd(n,16). Its decompositions are:

| r | G^ab |
|---|---|
| 2 | Z_(3L_(n/2)) |
| 4 | Z_(F_(n/4)) ⊕ Z_(15F_(n/4)) |
| 8 | Z_3 ⊕ Z_(L_(n/4)) ⊕ Z_(L_(n/4)) |
| 16 | Z_(L_(n/4)) ⊕ Z_(3L_(n/4)) |

F_0=0,F_1=1 and L_0=2,L_1=1, both satisfying u_(j+2)=u_(j+1)+u_j.

Literal full applicability bridge:

1. The successor's G_n(w) uses the cyclic shifts of w as relators. Substituting w=x_0 x_1 x_(n/2−1) gives exactly the defining presentation above. This is equality of presentations, with no quotient, sign change or parameter repair.
2. Every target n has gcd(n,6)=2, so satisfies the successor hypothesis. All indices are integral when used. Restrict throughout to the target n≥8; the displayed successor corollary omits that lower bound, so no claim about its small-n wording is needed. In particular n=4 would have F_1=1 and is outside our domain.
3. For r=2 the cyclic group has positive order ≥3, so d=1.
4. For r=4, write n=4k. Then k is odd and 3∤k. Since n≥8, k=1 is excluded, as is k=3; hence k≥5 and F_k≥5. Both factors are nontrivial and F_k divides 15F_k. A prime dividing F_k gives a two-dimensional quotient over F_p, while the displayed decomposition gives two generators. Thus d=2.
5. For r=16, k=n/4 is a positive multiple of four, k≥4 and L_k≥7. The same prime-divisor argument applied to L_k | 3L_k gives d=2.
6. For r=8, k=n/4≡2 mod4. The Lucas recurrence modulo three has period eight: 2,1,0,1,1,2,0,2; therefore 3|L_k. All three displayed factors have a Z_3 quotient. The mod-three quotient has dimension three, while the displayed decomposition supplies three generators. Thus d=3, including n=8 (k=2,L_2=3).

No exceptional admissible n remains. This establishes full subsumption independently of the author's proposed proof.

Proof content comparison: for r≠8 the successor splits t^n−1 into t^m−1 and t^m+1. The first resultant is three; coprimality from Lemma 4.11 separates the Smith factors. Modulo t^m+1, multiplication of f=1+t+t^(m−1) by the unit t yields q=t²+t−1. A companion-matrix swap reduces to q's 2×2 companion matrix, whose powers are Fibonacci matrices. Lemma 4.11 evaluates their entry gcd, and Lucas identities give the displayed factors. For r=8, coprimality at three fails; the proof instead swaps to the quartic (t²+t+1)(t²+t−1), uses a 4×4 block form, Cassini/Fibonacci identities, and Pisano congruences, obtaining Smith factors 1,3,L_k,L_k. Both residue classes n≡8,40 mod48 are treated. The proof was read through its conclusion; theorem and corollary displays were also checked visually in the PDF.

## Separate review dispositions

- **SOURCE: PASS (bounded).** Exact primary conjecture and presentations checked; complete relevant successor statement/proof obtained. Source hashes and byte sizes are retained separately. No MathDB request was made, so the live record is unverified.
- **MATH: full public subsumption established.** The bridge above covers the complete assigned domain. This is not a certification of every line of the author's independent proof. Once the exact subsumer was qualified, sustained algebra and further numerical checking were unnecessary.
- **SUBSTANTIVE: FAIL for discovery credit.** The complete endpoint and a stronger group classification are public. F1 (relation lattice as polynomial quotient), F2 (finite abelian group generator count via prime quotients), F3 (polynomial gcd over a field), multiplicity bookkeeping, and Lucas/Fibonacci computations do not rescue a resolved endpoint as a discovery.
- **PRIOR: resolved by positive primary-body evidence; RETIRE.** No claim of exhaustive literature coverage or earliest priority. The successor alone suffices. Current public-proof-registry clearance remains HOLD; its absence cannot erase the positive published resolution.
- **FORMAL-FEASIBILITY: not assessed for implementation.** A formalization would need the cyclic-presentation/abelianization bridge, finite abelian generator theory, and either the Smith-form companion machinery or the author's polynomial route. None was constructed, and no formal acceptance claim is made.

The requested adversarial audit of F1, finiteness, max_p dim(A/pA), characteristics 2/3/5, primes dividing n, repeated root five and degree-two-prime existence was conditional on surviving prior screening. It did not survive. These are not marked independently PASS; author proof correctness cannot restore novelty. No additional targets were solved.

The primary Theorem 4.2 prints 3(L_m−1−(−1)^m), whereas the successor proof uses the plus-sign resultant L_m+1+(−1)^m (with the separate factor three). The differing bytes were inspected. The source-order typo is not an outcome and is not used in the subsumption bridge.

## Provenance, coverage, failures and integrity

Flat retained originals: author-P2-339564.md, primary-1806.06821v2.pdf/.txt, successor-published.pdf/.txt. Only these scientific bodies were retained; no history/corpus tree copied. input-bindings.json freezes required inputs; flat-original-bindings.json links author originals, intake copies and these retained copies. Both intake and author manifests were independently checked, including exact file-set equality and allowed exclusions. All 398 direct original/copy pairs in intake bindings were hashed independently; their bodies were not scientifically reviewed. No upstream verifier was executed.

The primary PDF and derivative were bound before source reading; the successor PDF was bound before extraction and its derivative before searching/reading. SHA256/size are in source-provenance.json and the final manifest. The first manifest-shape checking helper failed with KeyError because the author manifest calls its exclusions `excluded_exact`, while intake uses `excluded_exact_paths`. The failed script is preserved as retain-v1-failed.py and the failure is recorded in failures.json. The corrected helper respects both explicit schemas and passed; no caps changed.

Search coverage: one early two-query public web search identified the exact successor. Search-engine snippets from barred domains were returned automatically but no such links were opened or fetched; only the accessible Aalto repository PDF was requested. No Google site, GitHub endpoints, ScienceDirect, MathDB, browser/account, TLS bypass or inherited parked route was used. No 403/429/challenge arose. No negative search hit is credited as novelty clearance. No registry retry was attempted. Access limits and failure chronology are retained in coverage.json/failures.json.

The separately executed local verify.py rejects byte/size changes, extra or omitted payloads, path escapes, duplicate entries and changed retained-source bindings. Its self-test deliberately mutates a payload in memory and requires rejection. Exact manifest covers every payload except manifest.json itself and final-receipt.json by actual filename. Integrity PASS certifies packet consistency only, not mathematics, novelty or acceptance.
