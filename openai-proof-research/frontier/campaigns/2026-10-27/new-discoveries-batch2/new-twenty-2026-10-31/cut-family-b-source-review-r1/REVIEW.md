# Independent qualification review: MathDB 353823

Review date: 2026-11-01 UTC. **Overall HOLD before major Lean investment. Ordinary mathematics PASS; exact v1/MathDB fidelity PASS; significance qualified PASS; bounded prior-art/version clearance HOLD; Lean feasibility plausible but substantial, endpoint absent. Zero accepted credit. Campaign remains 3/20 beyond 39.**

The overall HOLD is not a counterexample or an alleged missing ordinary lemma. The ordinary proof closes the exact claim using the established base-game theorem and even-cut invariance. The reasons to defer a large formalization are the incompletely compared published proof body and specialist successor coverage, together with the real cost of formalizing the base-game theorem. A small feasibility experiment on that dependency is reasonable; a major build should await the named comparison gaps. This review supplies no paper, publication, or acceptance.

## Scope, integrity, and review depth

Read the repository, batch, and twenty-result AGENTS; sources/upstream.json and the manuscript catalogue opening; the author SUMMARY, CUT-ORDINARY-PROOF, results[353823], raw/353823.jsonl, provenance/receipts, registry review, history notes, and relevant accepted-family lists. All **93/93 frozen-inputs.json bindings matched before and after**; detailed actual hashes are in bindings-before.json and bindings-after.json. No author files, ledgers, exclusions, protected candidates, git state, or other lanes were edited. No children, browser tabs, contact, upload, or publication.

Read all text of the retained 19-page Ellis–Thanatipanonda v1, including the entering/exiting transformations, every displayed Lemma 10/12 case, Corollary 13 proof, maps and tables in Section 5, Lemmas 16/17, Theorem 15, and Section 6–7. This is a proof-body comparison, not a fresh certification of every published dependency or a replay of its Maple computations. Read DDLP v3 AP definition, Lemmas 10/11, full Theorem 9 and Proposition 13 proofs; Lemma 12's full auxiliary proof and every other DDLP section were not independently audited. Read the entire retained Omega Family A module and its current problem dossier. No Lean module was compiled or its transitive closure audited in this review.

## Exact statement and source versions

For nonempty natural sets X,Y, every member of X is even and at least 4, every member of Y is odd and at least 5. Define x=min X=2c, c≥2, y=min Y, and suppose 3x<y. With C={1}∪X∪Y, prove actual normal-play heap values G_C(n)=G_{ {1,x} }(n) for every n≥1. There is no finiteness restriction. Natural well-ordering supplies both minima and x∈X; parity supplies the integer c. Every member of Y is ≥y>6c.

The frozen raw MathDB statement and v1 Section 7 Conjecture 2 agree in these quantifiers. Definitions 1–2 mean d cuts create d+1 positive parts with unchanged total, and option values are xor values under that same game's recursion. Normal play is explicit. The author has not substituted the nearby arithmetic-periodicity question or Family A.

Primary local PDF: https://arxiv.org/pdf/2203.02457, retrieved 2026-11-01 13:16 UTC, SHA256 **bdc77505379e1c9255cabb4686d074d4d5fb5081ee276d7f7a7ea8f0d69cb8be**; its internal banner is 2203.02457v1, 4 March 2022. Live abstract/history was retrieved anew (http-receipts.json). The author-posted published paper is Discrete Applied Mathematics 322 (2022), 391–403, DOI 10.1016/j.dam.2022.08.027. Indexed primary-PDF extraction independently confirms Section 7 and the full Lemma 18/Theorem 19 induction; published Section 4 calls the old Corollary 13 **Theorem 13** and supplies the same partition recursion. See web-published-search.json and web-published-comparison.json. [Published author copy](https://thotsaporn.com/PartitionGame.pdf).

Direct published-PDF download timed out in the author run and again under this review's 18-second HTTP bound; web open also timed out. No local PDF byte hash is claimed. The full published pages 398–401 and complete revised proof were not obtained/read; indexed selected passages are not a complete version diff. DDLP's retained PDF is arXiv:1803.02621v3, 15 May 2020; live history confirms v3 is the last listed revision, with journal reference DAM 285 (2020), 509–525. The journal landing extraction exposes AP statements, but the direct ScienceDirect open returned 403 and was not retried. [DDLP record](https://arxiv.org/abs/1803.02621).

## Independent ordinary proof audit

Write g for the **actual** {1,2c} game. Take Theorem 3 as a published input: its six blocks and period/saltus are exactly the author formula. Set

    W(8q+4a+2b+e)=12cq+(4c+1)a+2cb+e,  a,b,e∈{0,1}.

For completeness, here is a symbolic index audit. In block j use n=2cj+2t+1 or 2cj+2t+2, with 0≤t<c. The deficits n−W(g(n)) are:

| block j | odd position within block | even position within block |
|---|---|---|
| 0 | 2t+1 | 2t+1 |
| 1 | 2t+1 | 2t+1 |
| 2 | 4c if t=0; otherwise 2t−1 | 2t+1 |
| 3 | 4c+2t | 4c+2t+2 |
| 4 | 4c+2t | 4c+2t |
| 5 | 4c+2t | 4c+2t |

Thus 1≤n−W(g(n))≤6c on the first period; the upper endpoint is attained at n=8c. Block 3's exceptional n=4c+1 and the following n=4c+2 are both included. The author's coarse block-5 lower bound is weaker than the exact 4c, but valid. At c=2 all ranges remain valid, including the single post-exception odd entry. No c≥3 argument is being silently used here.

For every n≥1 use q=(n−1)/(12c), r=(n−1) mod (12c)+1. Then n=12cq+r, 1≤r≤12c, and iteration of Theorem 3 yields g(n)=8q+g(r). Since g(r)<8, the low three digits do not carry into q, and W(g(n))=12cq+W(g(r)). This proves the deficit bounds for arbitrary n and arbitrary-size q. Ordinary addition of 8 during period iteration can carry *inside q*, but W's high part is linear in the entire quotient, so this causes no defect.

Xor subadditivity requires no condition on adjacent weight sizes. At each binary place the output digit is the parity of the number of input 1 digits, hence at most that number. All weights 1,2c,4c+1,12c,24c,... are positive; every natural input has finite support. Summing establishes W(xor_i v_i)≤ΣW(v_i) for every finite list. This also proves the large-q claim without a finite bit-width assumption.

If positive h_1,...,h_p sum to n and xor_i g(h_i)=g(n), then

    W(g(n)) ≤ ΣW(g(h_i)) ≤ Σ(h_i−1)=n−p.

Consequently p≤n−W(g(n))≤6c. An added odd cut d∈Y has d>6c, so its option has p=d+1>6c and cannot have xor g(n). No assumption that this xor is numerically less than g(n) is needed; W need not be monotone in the natural order.

Put C0={1}∪X. Theorem 19 gives G_C0=g, including infinite X. Strong induction on n now proves G_C=g. Every legal part is <n because d≥1 and at least two parts are positive. Under the induction hypothesis the full C-option values are base g-xors. Old C0 options still realize every k<g(n) and exclude g(n); all newly added options exclude g(n) by the part-count bound. Hence the mex is exactly g(n). At n=1 no cut is legal. At each n, d≤n−1, p≤n, and all h_i≤n, so the legal option set is finite even for infinite X,Y. Its mex exists. Nothing depends on enumerating either infinite cut set. This is a complete ordinary argument, with its two published inputs identified.

## Prior arguments, overlap, and significance

The v1 proof of Theorem 3 obtains the base values by the entering/exiting machinery and shifted-expanded correspondence with c=3, not by W. Lemma 18 reduces the number of parts by **two**; Theorem 19 iterates it for extra even cuts, whose part counts are odd. Neither statement provides the required exclusion for added odd cuts with even part counts. Corollary 13 changes both total size and part count, so using it does not by itself close a same-total mex exclusion. The published selected bodies preserve these distinctions.

DDLP Theorem 9 assumes AP verification for the game's own values and bounded maximal cut; Proposition 13 supplies AP3 from AP1/AP2 and cuts of both parities within its specified range. Their proofs rearrange quotient/remainder contributions and equal pairs. They do not prove AP1/AP2 uniformly for Family B, identify its initial block values for every c and arbitrary Y, or handle unbounded cuts directly. Finite truncation could extend a *proved uniform finite-game* result to infinite cuts, but that missing uniform result cannot be replaced by numerical checks. Thus no complete full-scope subsumption bridge was found in these bodies. A generic AP test is not this solution.

Omega Family A is a genuine prior full-family proof, committed 2026-10-21 at 8908653c036b89bc19b0e25585f3e1c43e3c19b7. It assumes cut 3 and proves F(n)=2 floor((n−1)/(2c))+(n−1 mod 2). Its `odd_exclusion` uses parity; `quotient_budget`/`large_exclusion` use xor≤sum and quotient budgets. These are related proof ideas and must be acknowledged. The reachability proof explicitly invokes cut 3; deleting that cut changes both the formula and the exclusion geometry. At c=2,n=9 Family A gives 4 whereas this base game gives 1. Its private theorems are specialized to F, not arbitrary g or arbitrary binary-place potentials. Generalizing them to this W still requires the nonuniform low-bit weights, six-block defect bounds, and actual-base-game bridge. The similarity is not a demonstrated routine full-scope deduction. [Current pinned Family A dossier](https://github.com/the-omega-institute/trureturing/blob/9e440b1c5cc46060c48d9f6896736db2b2c7175e/Problems/ellis-thanatipanonda-2022-cut-family-a-conjecture-1.md).

Adjacent r492 reviewed 353822 and held its Family A route; it did not reject or solve 353823. Historical accepted-list screening covered 30 prior first-campaign entries, 9 batch entries, and 3 present-campaign entries; no cut-game family overlap was found in those accepted lists. Inherited exact-ID/title checks remain bounded, not whole-history clearance (historical-screen.json).

**Significance: qualified PASS.** The additional mathematical content is a tailored weighted certificate that translates a nonmonotone, exceptional-block sequence into a uniform arity obstruction. Once discovered, its verification is short; that does not make it a substitution into Theorems 3/19 or the AP test. The xor inequality and mex-extension principle are standard. The substantive candidate contribution is their particular weighting/defect fit and its application uniformly over all parameters and infinite cut sets. This is a modest exact conjecture resolution, not a new general theory or a claim of worldwide priority. The source's open label alone supplies none of this conclusion. No routine-consequence FAIL is justified by the bodies read.

## Current registries and bounded clearance

At 13:30 UTC OpenAI/math remains 4eaee87548250b2682affda7d05d947c05554bae (commit time 2026-10-30). The verified complete preprints tree has 13,578 entries, not the truncated root cache. Relevant path screening found no matching cut-game manuscript; this is not a whole-manuscript content search.

Omega now has head **9e440b1c5cc46060c48d9f6896736db2b2c7175e**, commit time 13:25:50 UTC, replacing the supplied 13:15 head. The compare response has 27 commits and 18 changed files, all vertex-algebra artifacts; four D5/S3 Lean additions and no Problems changes. Reusing the verified complete older D5/Problems inventories (13,297/1,629 entries), plus both recorded deltas, is valid for the scoped Family A/B path screen. It is not a complete current repository-body/history audit. Family A's module is unchanged across this delta. Read its current dossier; it expressly excludes Family B from its settlement. No counterpart of Conjecture 2 was found in the inspected paths.

Targeted public searches found no exact Family B proof. One search lead, scinet-ai/math-combinatorial-games, was checked by its complete untruncated 34-entry tree and pinned README; it concerns hexadecimal games, not this theorem. Its other proof files were not read. No exhaustive forward-citation or all-author-successor-body search is claimed. Public route errors, dates, received-byte hashes, and URLs are in http-receipts*.json and web-*.json. A web extraction is a text receipt, not a hash of unseen PDF bytes. No denied MathDB/JKU/Palomar route was retried. The ScienceDirect 403 was respected.

**Prior-art/version verdict: HOLD.** Material remaining work is a lawful complete published Ellis–Thanatipanonda proof comparison, especially revised Section 5, and a bounded explicit successor/citation-body comparison. DDLP journal proof differences beyond the exposed AP sections also remain unverified. None of these gaps is evidence of an existing solution; they limit the clearance claim. This review does not use an inaccessible abstract as clearance.

## Diagnostics and formalization bridge

Independent diagnostics.py calculates actual mex recursively using exhaustive sets of xor values of ordered positive compositions, then compares the result with the formula. It tests c=2,3,4,7, n=1..80, both {1,2c} and the maximal allowed cut set truncated to legal cuts at each heap. All eight sequences pass. Additional potential tests cover c=2,3,4,7,31,100, every n through three periods, selected q=2^100+2^51+7 boundaries, and xor pairs through 127 plus 100-bit adversarial values. Full outputs are diagnostics.log/json. These are diagnostics only; the symbolic proof above proves the general assertions. Run used at most two affined CPUs, 768 MiB address-space limit, 70 CPU seconds and 85 wall seconds, finished in under one second. HTTP scripts used two threads, 768 MiB, 60 CPU seconds, 65 wall seconds, 18 seconds per request, 16 MiB per response, and completed synchronously.

Conditional full Lean bridge plan (not an existing endpoint):

1. Define actual G(C,n) by well-founded recursion, with finite positive lists summing to n and length=d+1 for d∈C. Prove every legal part<n for positive cuts, finiteness at fixed n, mex exclusion and coverage, and agreement with normal-play disjunctive xor semantics. An arbitrary set C is allowed; do not require a Fintype C. Reject zero cuts in the hypotheses or prove the recursion guard inactive.
2. Define the six-block candidate f_c on positive n using q=(n−1)/(12c), residual r, and the exceptional third block. **Prove G({1,2c},n)=f_c(n) for every c≥2,n≥1.** Port Theorem 3's full dependency chain: finite AP certificates for c=2,3; Proposition 4; entering/exiting lemmas and recursion; Section 5 maps, Lemmas 16/17 and Theorem 15. Explicitly cover exceptional residues, remainder carries and the finite nim-set tables by kernel-checkable proofs. DDLP test-based base cases require their complete hypotheses, not observed tables. An alternative direct proof for actual G of the two potential bounds would be welcome, but no such independent shortcut has been established here.
3. Prove Lemma 18 for actual base-game nim-sets from the established recursion and Corollary 11. Iterate to every even d≥2c and formalize Theorem 19 for arbitrary nonempty even X with minimum 2c. Strong induction and option-set containment avoid any infinite-union finiteness assumption.
4. Define W by quotient/remainder bits. Prove xor subadditivity via repeated `Nat.xor_div_two`/low-bit lemmas or a finite-support bit sum; extend to lists. Prove the symbolic deficit table and period cancellation from the proved actual-game formula. Natural subtraction must be justified by W(g(n))<n, or state the inequalities as W(g(n))+1≤n≤W(g(n))+6c.
5. Derive the arity bound using positivity and sum of predecessors. Prove the mex extension by strong induction for C0⊆C, rewriting actual smaller-heap values. Obtain x,y minima from nonempty sets, even x=2c and c≥2, then y>6c and d≥y for d∈Y. Conclude precisely the MathDB equality for every positive n, without assuming finiteness of X,Y.
6. Pin Lean/mathlib, independently review the final literal statement and game definition, audit all transitive axioms, and perform a clean extracted rebuild. Only propext, Classical.choice and Quot.sound are allowed. No assumed sequence axiom, surrogate predicate, sorry, unsafe or native_decide endpoint is admissible.

The author's environment records Lean 4.34.1 / mathlib d13f23b723b8a846827a245b89c10fc7d3f11612; this review has not built against them. Steps 1 and 4–5 look manageable, with audited infrastructure reusable from Family A. Step 2 dominates risk and effort; the read long-case proof is a material semantic obligation, not an implementation detail. Step 3 also requires actual nim-set lemmas. **Lean feasibility: qualified plausible, current formal completion HOLD.** Do not confuse an easy formalization of the final potential argument with a complete game theorem. Recommend closing the precise prior comparison gaps and testing one base-game dependency before committing major resources.
