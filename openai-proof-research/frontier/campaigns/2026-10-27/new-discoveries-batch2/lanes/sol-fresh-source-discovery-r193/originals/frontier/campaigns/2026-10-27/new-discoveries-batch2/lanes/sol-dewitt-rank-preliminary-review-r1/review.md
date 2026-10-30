# Independent adversarial review: DeWitt–Keith rank congruences

Review date: 2026-10-29 UTC. Solo; no children. Recommendation: **ordinary mathematics PASS for the numbered preprint Conjecture 1; substantive discovery FAIL under this campaign's strict routine-adaptation rule. Do not invest in Lean or a paper for this nomination.** Journal equivalence and current prior-art clearance remain HOLD. This is a review recommendation, not a root exclusion, acceptance, or count change. Baseline remains 8 additional / 38 total, candidate credit zero.

## Binding and scope

I independently read PROOF.md, discovery.md, the actual relevant preprint HTML body (definitions, Section 3 including Lemmas 6–8, Section 4 Lemma 9, and Section 5), and Keith's actual Theorems 1 and 5 in the frozen v4 PDF text. The 29-file manifest was checked against the source lane before copying; every own-copy byte matched. PROOF SHA256 is `4df5407257fb81a205974c7e484cfaf5c04278537114f0dc7dbadc5fbe6b7d59`. Final verification is recorded separately. Ancestor/batch AGENTS, NEXT, ledger and prior-campaign context were read; context hashes are in context-inputs.json. No shared or source-lane files were modified.

The target is https://arxiv.org/html/2507.13566v1, Section 5 numbered Conjecture 1, on partitions `(a^c b^d)` with integers `a>b>=1,c,d>=1,ac+bd=N`. The statistics are exactly `r=a-c-d` and `s=a+b-2c-d`. For every integer n>=0 and `(A,B)` in {(16,14),(36,30),(72,42),(196,70),(252,114)}, both s-parity counts at N=An+B must be divisible by four. The same holds for r on the last four progressions. The exclusion of the first progression is not a universal nondivisibility assertion. No quantifier was weakened; n=0 is included and all N are positive.

The prose following the numbered conjecture additionally concerns each statistic's residue-zero class modulo four. It is outside the numbered theorem environment and is **not established** by this candidate. Even-count divisibility is only divisibility of the sum of residue-zero and residue-two counts. Conjugation negates both statistics, so it relates residues one and three but supplies no separation of zero and two. Any handback claiming that whole surrounding prose is resolved would fail fidelity.

## Independent all-order bridge and map audit

Here is the complete bridge, including the steps supporting the routine-adaptation finding. Numerical checks below are not used in it. Write N=2m, m odd, and let X,Y,Z count OEOE,OEEO,EOEO in the source's size/multiplicity order.

1. Both products ac,bd must be odd, or both even. In the latter case exactly one is 2 modulo four and the other is zero. The nine possible parity words are OOOO, EOOE, EEOE, EOEO, OEEE, EEEO, EOEE, OEOE, OEEO. Inspection of r and s modulo two and the conjugation pairings gives `E_s=2X+Y`, `E_r=2Z+Y`. Conjugation is `C(a,c,b,d)=(c+d,b,c,a-b)`: all coordinates remain positive, the two sizes remain strictly ordered, weight is `b(c+d)+c(a-b)=ac+bd`, and direct substitution gives C²=id. It pairs EOEE with OEOE and EEOE with EOEO. These are precisely source Lemmas 1–3 and its Table 1 applied to the displayed statistics.

2. For X, write its pairs as `(a,2^i u),(b,2^j v)`, a,b,u,v odd, i,j>=1. Send these to `(2^i a,u),(2^j b,v)` and sort by size. Distinct odd factors a>b ensure distinct new sizes. The inverse divides each even size by its full power of two and multiplies that power into its multiplicity; it is defined exactly when the odd size factors differ. Sorting cannot erase pair information because the size coordinates distinguish the pairs on both sides. Thus it is a bijection from X onto the subset of Z with unequal odd size factors, exactly the source Lemma 9 map, not an assumed injection without inverse.

For the complement in Z, equal odd size factor k gives sizes `2^(t+1)k,2k`, t>=1: the smaller valuation must be one because N has valuation one. Multiplicities u,v are odd, and `m=k(2^t u+v)`. Conversely each divisor k|m and positive even x<m/k determines uniquely t>=1 and odd u from x=2^t u, with positive odd v=m/k-x. There are `(m/k-1)/2` choices. Consequently `Z-X=(sigma_1(m)-d(m))/2`, and **exactly** `E_r-E_s=sigma_1(m)-d(m)`. This agrees with source Lemma 9 because d(2m)=2d(m).

3. Let S consist of `(a,c,b,d)` with `a=2 mod4`, c,b odd, `d=0 mod4`, `a!=2b`. In X exactly one multiplicity is 2 mod4. Double its size and halve that multiplicity. If it is the larger size, the image is the part of S with a>2b. If it is the smaller size and becomes larger, the image is the part of S with a<2b. Otherwise the image is the subset Y1 of Y whose even size has valuation one. An odd size never equals twice an odd size, so no tie is possible. Halving the unique even size and doubling its odd multiplicity gives each inverse and the required branch. All images preserve positive integer coordinates and weight. Thus X=|S|+|Y1|. In Y the even size and even multiplicity have valuations one and at least two in opposite orders; C interchanges them and bijects Y1 onto Y\Y1. Hence Y=2|Y1| and `E_s=2|S|+4|Y1|`. This is the source Lemma 6 reduction, with its two inequalities combined into S.

4. Conjugation sends S bijectively to W consisting of `(u,x,v,y)` with all entries odd, `u>v>=1`, `u=v mod4`, `x=y mod4`, `x!=y`, and `ux+vy=N`. Explicitly `(u,x,v,y)=(c+d,b,c,a-b)`. Conversely it produces `(x+y,v,x,u-v)` in S; in particular x+y=2 mod4, u-v=0 mod4, and x+y!=2x. These formulas settle positivity, distinctness and both congruence conditions without invoking a diagram.

On W transpose each size/multiplicity pair and sort by the new size. Since x!=y it is defined; since u!=v the new multiplicities remain distinct. The two congruences are symmetric under this operation and sorting, and applying it twice restores the original sorted pairs. A fixed unordered two-element set of pairs under transpose either has both pairs individually fixed (`u=x,v=y`, N=u²+v²), or exchanges them (`u=y,v=x`, N=2uv). These are exhaustive because transpose acts as a permutation on two pairs. They are the **same two types explicitly classified in source Lemma 8**.

Assume now N is not a sum of two integer squares. The first type vanishes. For the crossed type u>v odd, uv=m and u=v mod4. If m=3 mod4 there are none. If m=1 mod4 every factor pair has equal residues modulo four. Also m is nonsquare, since a square m would give N as two equal squares. Hence exactly d(m)/2 unordered factor pairs remain. Nonfixed orbits have size two, so `|S|=0 mod2` for m=3 mod4 and `|S|=d(m)/2 mod2` for m=1 mod4. Therefore

`E_s=0 mod4` when m=3 mod4; `E_s=d(m) mod4` when m=1 mod4.

The factor 2 from step 3 is essential. Merely asserting that Lemma 8 remains fixed-point-free would be false, for example at N=10. The candidate retains exactly the correct correction term.

5. At N=16n+14, m=8n+7 is 3 mod4 and N=6 mod8 cannot be a sum of two squares. Thus E_s=0 mod4 directly. For the other four rows, respectively write

| N | m=p h | why h is nonsquare |
|---|---|---|
|36n+30|3(6n+5)|h=2 mod3|
|72n+42|3(12n+7)|h=3 mod4|
|196n+70|7(14n+5)|h=5 mod7|
|252n+114|3(42n+19)|h=5 mod7|

In every row p does not divide h. The listed primes are 3 modulo four; inspection of quadratic residues modulo 3 or 7 shows that p dividing a square sum forces both coordinates divisible by p. Valuation one of p in 2ph therefore rules out such a sum. The last column excludes squares of h. Pairing divisors of nonsquare h gives d(h) even. Each divisor of ph is uniquely e or pe with e|h, so `d(m)=2d(h)=0 mod4` and `sigma_1(m)=(p+1)sigma_1(h)=0 mod4`. Step 4 gives E_s=0 in either m residue, and step 2 then gives E_r=0, on all four rows, for every n>=0.

6. The known unrefined totals give the odd counts by subtraction. The dependency is exactly https://arxiv.org/pdf/1502.00366v4, Theorem 1, PDF p2, for the last four rows, and Theorem 5, PDF p3 (also DeWitt–Keith Theorem 1), for (16,14). Both count exactly two *distinct sizes*, with no parity restriction. They assert the required modulo-four total congruences, not just modulo two or an eventual range. Their source proofs are upstream inputs, not novel work here. This candidate does not give a new wholly combinatorial proof of those four unrefined totals.

No ordinary gap remains in this bridge. There is no need for an unproved analytic bound, generating-function inference, numerical extrapolation, or extra hypothesis beyond the stated known totals.

## Substantive gate: FAIL, with reasons and falsifier

The bridge above is complete but routine relative to the supplied source. Steps 1–3 are direct extractions of source Lemmas 1–3, 6 and 9, plus inspection of the proposed statistics. Step 4 uses precisely the source's conjugation/reversal/conjugation and its already explicit exhaustive fixed-point classification. The only extension is to retain the crossed factor pairs instead of ruling them out by N=6 mod8, count them as d(m)/2 when m=1 mod4, then use elementary divisor pairing and the four displayed residue obstructions. Step 5 and total subtraction finish the exact requested endpoint. No replacement involution, new structural classification, new arithmetic estimate, or uniform unresolved bridge is introduced.

The strongest contrary argument is that the source itself conjectures the endpoint and says its main proof does not immediately generalize. This is real evidence that the rank consequence was not printed there. It does not establish campaign eligibility: the candidate imports the old total theorem and only refines its parity counts, rather than generalizing the entire source's main combinatorial proof. Its correction term is mathematically useful but arises by counting the very exceptional family the source already identifies. Under the explicit campaign rule excluding routine corollaries/adaptations, I recommend exclusion of this nomination, without asserting a previously published identical theorem. Shortness alone is not my reason; the six-step derivation above identifies every actual dependency and residual step.

A falsifier of this assessment would be a demonstrated essential missing step in this reduction, or an independently stated stronger result requiring structure beyond these inherited maps and elementary factor-pair counts. Merely formalizing these steps, proving more small instances, or relabeling the same parity theorem would not falsify it. A mathematical falsifier is a failed map/inverse/fixed-point classification or any required source-progression parity count nonzero modulo four. None was found.

## Sources, versions and current prior limits

Live arXiv abstract retrieval at 2026-10-29T18:35:35.105979+00:00 still shows only v1, submitted 2025-07-17 23:02:26 UTC; its SHA matches the frozen abstract. This does not prove equivalence to the journal. Publication DOI https://doi.org/10.1142/S1793042126500569 is identified with IJNT 22(5) (2026), 1075–1084.

A legitimate institutional route, https://digitalcommons.mtu.edu/michigantech-p2/2399/, retrieved 200 at 18:35:35Z, supplies publication metadata but sends its full-text link to the DOI; it is not an author manuscript. I did not revisit the inherited blocked World Scientific full-body route.

The public World Scientific-supplied ResearchGate preview at https://www.researchgate.net/publication/399831893_Combinatorial_proof_of_a_congruence_for_partitions_into_two_sizes_of_part exposes **only page 1075**, not Section 5. The web reader obtained its actual introductory page; it reports revision 27 October 2025, acceptance 9 December 2025 and publication 12 February 2026. The local HTTP copy is 403, preserved as such, not represented as the preview text. Clicking the public preview link failed with 403; no retry, account, contact or bypass followed. These dates make post-v1 changes plausible. The actual journal conjecture, definitions, fixed-point proof and possible version changes remain **unread/HOLD**. The first-page preview cannot clear this hold. Web observations are recorded in web-observations.json separately from locally hashed HTTP evidence.

The frozen follow-up https://arxiv.org/html/2604.25394v1 was checked at its actual Theorems 1/4 and concluding Conjecture 7: they concern a square/divisor sum and an unrefined nu_2 term, not these rank-parity counts. This comparison does not purport to rule out all semantic implications of its proof. Likewise the actual cached registry bodies DivisorCountPrimeFactorBound and MixedParityBlockPartitionProduct concern a divisor-count lower bound and mixed blocks of *set* partitions; their displayed endpoints are not these integer-partition statistics. Badges were not used as mathematical evidence.

The supplied root checkpoint at 18:13 had complete old inventories; inherited r81/r82 chronology already invalidates any inference of current completeness. New direct live GitHub HTML at 18:35:35Z reports Omega head `23a4ae6f843d1635869b7656fb6bd681121447a8`, newer even than r82's `ab5c4b29ee890cea082643b8467cac3b0f7fd85a`. Correct OpenAI repository https://github.com/openai/math at 18:36:16Z reports unchanged `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`. An initial mistaken owner/title URL returned 404; it is recorded and supplies no evidence. No new complete Omega tree or semantic delta was audited. Current public-registry clearance remains HOLD. No git operations were used, and Blueprint is not identified with Lean. Negative web search is not priority evidence.

## Independent finite validation and per-gate disposition

The own checker enumerates rectangle areas k,N-k and factors each independently to obtain the two sizes and multiplicities. This differs from the submitted size/multiplicity-first enumerator. It checks exact set images of the valuation map and the partial-doubling map, conjugation, the W constraints, reversal involution and both fixed-point types. Results: 84 N cases up to 1122; 305356 conjugation checks; 30339 valuation-map checks; 19858 S-map checks; 56 nonsum-of-squares formula cases; 47 progression rows. PASS. These tests support debugging only; the all-order proof is above. Guard reports 20971520-byte sampled peak group RSS and 0.522 seconds. All custom helpers ran under the copied unchanged guard: AS/group RSS 512MiB, CPU210s, wall230s, nominal40ms sampling, BLAS1. Two failed text-extraction attempts (missing bs4 and missing math alttext) were corrected using standard-library extraction; neither was a mathematical failure. Sampled RSS cannot exclude between-sample transients.

| Gate | Disposition |
|---|---|
|Ordinary proof, numbered v1 scope|PASS, using exact known total theorems|
|Source definitions/quantifiers, v1|PASS; residue-zero prose explicitly excluded|
|Published-body equivalence|HOLD; only journal first page recovered|
|Substantive discovery|FAIL; complete routine source-adaptation bridge above|
|Bounded/current novelty|HOLD; no full current Omega audit or worldwide-priority claim|
|Formal endpoint / extracted replay|NOT ATTEMPTED; no eligibility to invest|
|Paper / acceptance / credit|NOT ATTEMPTED; root alone decides, credit remains zero|

No Lean estimate is offered because the substantive gate fails. Nothing in this report changes campaign counts or clears inherited source holds.
