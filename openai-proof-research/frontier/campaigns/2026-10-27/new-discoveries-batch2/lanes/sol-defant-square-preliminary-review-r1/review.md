# Independent preliminary review: Defant prime-square exclusion

Review date: 29 October 2026. SOLO review, no children. **Recommendation: do not invest in the campaign certificate; substantive FAIL (routine adaptation).** This is an eligibility judgment, not a mathematical refutation or a claim of an earlier published full proof. Root alone decides acceptance. Candidate credit remains 0; counts remain 5/30 additional, 35/60 total.

| Gate | Verdict | Meaning |
|---|---|---|
| 1 Source | PASS | Actual journal definitions, dependencies and full conjecture verified. |
| 2 Ordinary mathematics | PASS | Complete argument for every positive integer r and every prime p, with published prime-gap input. |
| 3 Prior proof / novelty | HOLD | Corrected complete Omega snapshot screened, but neither current-head nor comprehensive semantic clearance established. No earlier full proof located in the bodies inspected. |
| 4 Substantive eligibility | FAIL | Complete adaptation of the source's own replacement proofs, detailed below. This judgment is contestable against the campaign's permissive short-proof precedents. |
| 5 Formal feasibility | HOLD | No closed endpoint. Stronger prime-interval bridge missing; assessment stopped at useful scope after gate 4. |

## Frozen object and independence

The supplied root manifest (created 09:26:21 UTC, supplied revision c03d73c5cb) names 29 files. Every file was SHA256-verified before copying, bytecopied into `candidate-copy/`, and verified there; final verification again checks both original and copy against the same manifest. `hashes-before.json` and `hashes-after.json` record this. No git command was run; revision attribution is supplied metadata, not an independently read git state. The unfrozen candidate `__pycache__` is not part of these 29 files and was not copied or executed.

I read both governing AGENTS files, current NEXT standards and ledger/context entries including the accepted Simon-threshold and Schmidlin/Gamma boundaries. The initial combined context output was truncated; focused reads recovered the relevant current standards and acceptance descriptions. I do not claim a line-by-line audit of the entire historical campaign. Root's ROOT-NOTES and checks.json were read as objections/evidence, not inherited proof. `own-check.py` is independently written, imports no candidate code, and was launched with BLAS thread counts 1, 512 MiB AS, 25 seconds CPU and 40 seconds alarm, under a 45-second outer timeout.

## Gate 1: actual source, PASS

Primary journal: Colin Defant, *On Sparsely Schemmel Totient Numbers*, INTEGERS 15 (2015), A18, published 8 May 2015, [publisher PDF](https://math.colgate.edu/~integers/p18/p18.pdf). The frozen PDF hash is `11e60fb876215964d01a312431faff98f076b187fb15dd23ce342804fd16a482`. I personally rendered and visually read complete relevant journal pages 1, 2, 6, 7, 8; the images are in `evidence/journal-*.png`. The PDF skill was read before rendering.

Page 2 defines B_r as the positive integers with all prime factors greater than r, including 1, equivalently S_r(n)>0. S_r is multiplicative with S_r(l^e)=l^(e-1)(l-r) for l>r, and zero for l<=r. Definition 1.1 requires **strict** S_r(n)<S_r(m) for every m>n in B_r. A larger witness with equal value defeats membership. No squarefree or coprimality assumption applies to the candidate n; coprimality is required when evaluating the witness multiplicatively.

Printed page 8 Conjecture 1 quantifies over **every prime p and positive integer r** and asserts p² not in F_r. It is not MathDB329433's conjecture about the largest prime's cube dividing arbitrary n. Independently extracted preprint arXiv1412.3080v1 has the same definitions and argument bodies with different numbering: Lemmas 3.1/3.2, Theorems 3.1/3.2, and Conjecture 3.1 on printed page 9. No target-scope difference was found.

Journal Lemma 2, page 6, says p_(j+1)/p_j <= 7/5 for j outside {1,2,4}. Its proof uses Dusart's interval theorem for x>=396738, substitutes x=p_j+1 for the large range, and checks the remaining primes computationally. The manuscript's analytic dependencies are accepted ordinary antecedent truth as instructed; I have not re-audited Dusart's analytic estimates or antecedent prime-gap tables. My independent sieve verifies the entire small base through starting primes <=396738, with 33,608 pairs and exactly the exceptional pairs (2,3), (3,5), (7,11). This differs from candidate/root finite-check counts because of the chosen inclusive range; it is not a contradiction.

## Gate 2: complete independent derivation, PASS

If p<=r, S_r(p²)=0, so p² is outside B_r. Otherwise choose a, the least prime greater than r. Prime infinitude gives existence; leastness and p>r give r<a<=p. Bertrand gives a<=2r, including r=1,a=2.

Put x=p²/a and let q be the least prime strictly greater than x. Existence follows from prime infinitude (or Bertrand applied above x). Since a<=p, x>=p>=a. Thus q>p>=a, q and a are distinct primes greater than r. Consequently m=aq is an integer in B_r, m>p², and exactly

S_r(m)=(a-r)(q-r), whereas S_r(p²)=p(p-r).

For x>=11 choose u, the greatest prime <=x. It exists because 11<=x. Then u>=11, and q is its successor, even when x is itself prime. The source exceptions concern u=2,3,7 only. Hence q<=7u/5<=7x/5<3x/2. No integrality of x was assumed.

Write d=p-a>=0. Direct expansion, or subtracting the quadratic at p=a and collecting powers of d, gives

2a[p(p-r)-(a-r)(3p²/(2a)-r)]
 = (3r-a)d² + 2a(2r-a)d + a(a-r)(2r-a).

All three terms are nonnegative because a<=2r, r>0 and a>r; 2a>0. Since a-r>0 and q<3p²/(2a), S_r(m)<S_r(p²). This settles the entire unbounded range x>=11. `own-check.py` separately verifies equality of all multivariate polynomial coefficients after clearing 2a; it does not just test sample values.

If x<11, p<=x<11 forces p=2,3,5,7. Enumerating 1<=r<p and the condition p²<11a gives exactly these witnesses, ordered (r,p,a,q,m,S_r(m),S_r(p²)):

```
(1,2,2,3,6,2,2)       (1,3,2,5,10,4,6)
(2,3,3,5,15,3,3)      (2,5,3,11,33,9,15)
(3,5,5,7,35,8,10)     (3,7,5,11,55,16,28)
(4,5,5,7,35,3,5)      (4,7,5,11,55,7,21)
(5,7,7,11,77,12,14)   (6,7,7,11,77,5,7)
```

Independent trial division regenerates these rows. The two equality rows are essential and admissible. The polynomial sign argument, threshold partition, and these exhaustive small cases prove the full ordinary theorem; the additional 8,035 finite witness checks for 1<=r<=100 and p<=500 are diagnostic only. There is no uncovered boundary x=11, p=a, r=1, or p<=r.

## Gate 3: bounded prior-art assessment, HOLD

The strongest same-object primary evidence is the source itself. Actual Theorems 2 and 3 and their complete proofs were read, not just statements. Theorem 3 excludes a² for the *least* admissible prime a and all prime cubes. Lemma 3 descends exponents for membership; cube exclusion does **not** imply square exclusion. No existing theorem statement inspected directly subsumes all prime squares.

Masser–Shiu, *On sparsely totient numbers*, Pacific J. Math.121 (1986), pp407–426, actual page408, proves that every sparse Euler-totient record is even and the only power of 2 among them is 2, by explicit value-preserving replacements. This handles r=1, not arbitrary r. Defant's actual Miskolc companion *A Note about Iterated Arithmetic Functions*, Theorem 1 and its proof on p766, identifies the eventual {0,1}-valued limit with a prime-support indicator and proves complete multiplicativity. That concerns iterates, not suffix records.

A live author/citer search led to the actual 2020 publisher body *Enumerating cliques in direct product graphs*, Journal of Combinatorics11(2),351–358. I read Theorem 2.1 and its entire counting proof on pp355–356: clique extensions choose one vertex in each available multipartite class, giving a product formula. It cites A18 but does not provide the prime-square record conclusion. The author research homepage was fetched at 09:30:51 UTC; it directs readers to a CV/arXiv rather than listing relevant number-theory proofs. I did not follow every publication or establish an exhaustive citer list. The eigenstructure-of-sparse-matrices citer lead was not body-reviewed. These remain limits, not clearance inferred from titles.

Critical correction: r22 **does** contain complete D5 and Problems trees at Omega commit fb587b0e94c9169d5d1076c186dd766253eb5255 (commit 08:58:13 UTC). I verified their bytes against r22 provenance's artifact hashes:

- D5: 12,478 entries, not truncated, tree78600b30c936496511f27b46f7ebd96f34007741, SHA256 `7b2bd58009df41f9c6a7a362170310377bb462aed09a0ee8f38bbc32cdc93849`.
- Problems: 1,541 entries, not truncated, tree9f3d2d75496a0bc539877cf4aa5a07ccd7a20712, SHA256 `ddfdd290ee0b81f81926bb95d71fb321b51bdcc5bce8bdaa4384412fd60a8d41`.

These are the supplied approximately09:05 snapshot, not a new current-head observation. r22 explicitly discloses that its initial refresh HTTP log was overwritten; filesystem times around09:04:42 are **not** exact network receipts. The saved bytes, hashes, commit/tree binding and coverage survive. r25's assertion that the complete current snapshot was absent is corrected, without silently upgrading this to current semantic clearance. No GitHub API/tree/head retry or alternate-host retrieval was made during this review; the reported09:05 403/rate-limit constraint was respected.

I also hash-verified the complete AIM3541 tree at8729eab98bafe409b66c5e39253bf56569a62327, OpenAI13578 preprints tree at7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a, and Count183 tree atdbf673741a54c7dc9d88a6aec0e8148a538f4a3a. Exact paths/hashes and broad matches are in `evidence/registry-screen.json`. None has a named Schemmel/Defant/1412.3080/329432/329433 match. Generic totient and prime-square matches are not automatically excluded. Cached OpenAI totient-asymptotic source bytes were checked against the saved tree's actual Git blob hashes; its statements and inspected collision argument concern counting distinct Euler-totient values and common least-preimage prefixes. The other inspected OpenAI totient-fiber proof uses products of smooth shifted primes and pigeonholing, not Schemmel suffix records. This is a bounded content distinction, not a complete audit of those papers or generic registry files. Omega's broad matches have not all been body-reviewed. No new registry head was established.

Live searches on29October covered exact title, square-exclusion/proof terms, Defant followups, and site-restricted Omega/AIM/OpenAI/Count/clopen terms. No full counterpart appeared. The live clopen homepage at09:30:52 is byte-identical to r25's saved homepage and is not the entire corpus. Search queries and limits are in provenance. No badge, empty solution list, generic tree grep or stale/truncated tree is used as proof of novelty. Fenner remains excluded by Jin's14October actual proof; no Fenner badge analogy is used to approve this target. Chronology of a hypothetical later matching proof would require its actual commit/publication time and body; no such match was found here.

## Gate 4: substantive eligibility, FAIL recommendation

**Strongest case for PASS.** This resolves the precise full published conjecture, not a helper or changed endpoint. Source Theorem 3 expressly stops at the least-prime square and arbitrary cubes. Its cube proof cancels a factor p-r that is unavailable for squares. The new positive quadratic supplies the missing uniform comparison, including p close to a. A source author calling a statement a conjecture is evidence that it was not presented as an established consequence. Shortness, standard prime gaps, or the use of a classical identity alone cannot disqualify it.

**Strongest case for FAIL, and my decision.** Here the objection is narrower than “all ingredients are classical.” The source already performs the exact same-object construction at the exact square threshold: Theorem 3 chooses consecutive primes p_t,p_(t+1) with a p_t<p²<a p_(t+1), then uses a p_(t+1)p as a witness against p³. The candidate uses precisely its a and p_(t+1), and removes the trailing p to compare with p². For p=a, where the strict straddling equality needs separate handling, the candidate's strict successor convention works and the source already excludes a². Theorem 2's converse already uses the **two-prime** witness a p_(t+1), evaluates (a-r)(p_(t+1)-r), applies the **same Lemma 2**, and finishes by bounding a quadratic expression, with small r cases separately. Thus the construction, admissibility mechanism and refined prime-gap mechanism are already explicit, not a new reduction to a different theory.

Here is the complete adaptation, so this is not an assertion of similarity without a bridge:

1. Replace Theorem2's threshold p by p² and use the straddling primes chosen in Theorem3. Equivalently choose the strict next prime q>p²/a to cover p=a automatically. Retain the two-prime witness aq of Theorem2.
2. Replace Theorem2's comparison target p-r by the exact source prime-power value p(p-r). For x>=11, source Lemma2 gives q<=7p²/(5a)<3p²/(2a).
3. The only remaining comparison is an explicit scalar quadratic F(p)=p(p-r)-(a-r)(3p²/(2a)-r). Its leading coefficient is (3r-a)/(2a)>=0; at p=a its value is (a-r)(2r-a)/2>=0; its slope there is 2r-a>=0. Therefore F(a+d)=F(a)+(2r-a)d+[(3r-a)/(2a)]d²>=0 for d>=0. All signs follow from the same Bertrand a<=2r used in the source cube proof. This is the displayed identity without any new analytic or number-theoretic premise.
4. Handle p<=r by B_r and x<11 by the ten exhaustive rows above. These are the complete leftover cases; no conjectural or asymptotic bridge remains.

This is a complete proof **adaptation**, not a literal application of the theorem statements. I do not call it an already published full proof. The residual step is checking the value, slope and leading coefficient of the one quadratic obtained directly from the source's identical construction. Under the explicit campaign exclusion of routine corollaries/adaptations, I recommend substantive FAIL. The identity itself, Bertrand, source prime gaps and finite exceptions receive no separate credit. This failure does not diminish gate2 or justify discarding the valid ordinary proof.

**Acceptance-boundary reconciliation.** I read the accepted first-campaign Simon-threshold PROOF and parent final addendum, and Schmidlin PROOF/NOVELTY. Simon was accepted for a literal infimum-to-perspective-supremum reduction despite classical perspective convexity and a short final proof. Gamma was accepted for a uniform two-variable comparison and positive discriminant certificate beyond the classical remainder, with helpers uncredited. Consequently “one new algebraic inequality” or “few lines” cannot consistently be the rejection test. The distinction I apply is that Defant already gives the same replacement object, exact p²/a threshold, exact multiplicative comparison and same refined prime lemma in the immediately adjacent proofs; only their final scalar bound changes. Simon's accepted reduction changes the optimization representation, while Gamma's certificate treats the remaining two-variable parameter range rather than just modifying an existing same-source competitor estimate. This boundary is a judgment, not a theorem about importance. A root decision that the missing quadratic is comparable to those accepted bridges could reasonably overturn gate4; it must say so explicitly. I do not manufacture an earlier full theorem or use campaign count pressure to make this choice.

## Gate 5: formal feasibility, HOLD; bounded stop

The inspected pinned `frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/Mathlib/NumberTheory/Bertrand.lean` supplies `Nat.exists_prime_lt_and_le_two_mul` (line222). A bounded NumberTheory text/name search found no usable3/2 or7/5 prime-interval theorem; unrelated exponent3/2 occurrences do not qualify. This is not a proof of library-wide absence.

Blindly replacing q<3x/2 by Bertrand's q<=2x fails: at r=1,a=2 its upper bound for S_1(aq) is p²-1, larger than p(p-1) for every p>1. Even allowing finitely many small-r shortcuts does not make the same uniform quadratic valid under only a<=2r: at p=a, its deficit becomes (a-r)(r-a)<0. This demonstrates failure of that direct estimate, **not** impossibility of an alternate Bertrand-only proof with other witnesses. None was established here. Source cube proof's cancellation cannot repair the square comparison.

A full Lean certificate would need literal S_r/B_r/F_r definitions and multiplicativity at coprime prime products, strict successor and greatest-prime bridges, rational casts/denominator positivity, the sign identity and ten prime certificates. These are plausible finite algebra/number-theory tasks. The substantial unresolved dependency is a kernel-checked stronger interval theorem. One could develop an elementary short-interval proof using factorial/binomial or Chebyshev bounds, an explicit threshold and a finite prime-chain base; this requires new uniform estimates and a realistically bounded certificate, not just importing Bertrand or verifying a finite range. Alternatively, formalizing the Dusart route entails explicit analytic prime estimates and their verified finite inputs and is a large project relative to this candidate. No elementary interval proof or costed implementation plan was completed, no claim of impossibility is made, and no large formalization was started after gate4 failed. A cited published lemma closes the ordinary proof, but cannot enter an accepted Lean certificate as an extra axiom.

## Falsifiers and disposition

Mathematical falsifiers would be a non-strict source record definition, a hidden prime-gap hypothesis beyond j exceptions, failure of the strict-successor bridge, a sign error in the cleared identity, or a missing x<11 row. The actual source and independent checks resolve these objections. An earlier actual all-r prime-square theorem would independently exclude novelty immediately. The gate4 recommendation would need revisiting if the source construction does not actually carry over as shown, or if root applies the Simon/Gamma boundary to credit this precise residual comparison. A stronger prime interval theorem already present in the pinned library would reduce gate5 cost but would not itself settle gate3/4.

Preserve the valid ordinary proof and engineering evidence. Do not count, publish, contact anyone, or begin a large Lean endpoint on this review recommendation. Root retains sole decision authority. Only this review lane was written; no shared/candidate/other-lane writes, git operations, browser tabs, external mutations or agents were used.
