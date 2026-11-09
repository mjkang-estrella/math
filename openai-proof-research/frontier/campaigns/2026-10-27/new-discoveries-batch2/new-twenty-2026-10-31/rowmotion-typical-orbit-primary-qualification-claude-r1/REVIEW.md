# REVIEW.md — independent adversarial qualification of MathDB 368315

Reviewer: Claude Opus 5.5, high effort, personally. No children, programs, enumeration or Lean. Credit 0; campaign 58/80 beyond 39 prior, 97 total, unchanged. Root alone adjudicates.

## Recommendation: EXCLUDE AS ROUTINE OR CORRECTION (moderate confidence)

The author's theorem is correct and I reconstructed it independently. It should still not be credited, because the conjecture reduces completely to a classical order-ideal theorem by a short conjugacy that I derived here and that the author's self-review says was not found.

For interval-closed sets I with every row nonempty, whose image is also full,
    psi(I) := ( DCeil(I) U L(I), L(I) ),   L(I) := D(I) - I,
satisfies psi(Row I) = Row_J(psi I), where Row_J is ordinary rowmotion on J([m]x[n]x[2]). This needs no genericity. Sets with an empty row number O(n^(2m-2)), so at most O(n^(2m-1)) sets ever meet one within N+2 steps. Rowmotion on J([2]x[m]x[n]) has order exactly m+n+1 (Cameron and Fon-Der-Flaass; Striker-Williams Theorem 7.5; DPS Theorem 3.2), and short orbits are controlled by DPS binary-content resonance. Details: PROOF.md Section 4 and PROOF-ADDENDUM.md Theorem D.

This is my judgment under campaign precedent. It is NOT an authenticated earlier proof of Conjecture 4.1, and it is NOT a mathematical objection. The user or root may overrule it.

## Gates (kept separate)

| Gate | Result | Basis |
|---|---|---|
| Literal | PASS | Exact: every m>=1, orbit size exactly m+n+1, r(n)->1. Matches printed Conjecture 4.1, p.40. |
| Original source | PASS | Definition, conjecture, Section 4.1, Theorem 1.1 viewed as glyphs. |
| Final/correction | PASS, bounded | Current arXiv PDF is byte-identical to the frozen v1. No journal version searched for specifically. |
| Ordinary proof | PASS | Independent Route R; author's A1-A5 audited, no gap. |
| Prior proof | No proof of 4.1 found, bounded | Two searches, one query each. Not worldwide clearance. |
| Novelty | Not cleared | The conjugacy psi was not in anything read; bounded only. |
| Significance | FAIL under campaign standard | Complete reduction to a classical theorem, on top of a printed source plan. |
| Family | PASS, bounded | All 96 scopes compared on the displayed fields, no rowmotion or plane-partition overlap. |
| Formal | Not run, dormant | Assessment below. |
| Process | Qualified PASS | Disclosures below. |
| Acceptance | Root only | Credit 0. |

## Audit of the author

I found no mathematical error in A1-A5. Lemma A1, the enumeration, formula (R), the states B_s and A_s, the flip at time k, the arrival at time m, the matching rule, Proposition A3 and the count all agree with my independent derivation; my gap constant is m+1 and the author's m+2, a harmless difference. Bracketing of Theorem 1.1 is the printed one.

Errors or overstatements in A6, which is argument and not mathematics:
- A6(1) says pairs of order ideals do not reduce to order-ideal rowmotion on a product of chains. A reduction exists, using a product of three chains.
- A6's reply says the matching mechanism is absent. It is absent from the source, but the rule W=(W1)W2 -> W1(W2) is printed as rule (2) of Definition 7.6 of Striker-Williams, attributed to Cameron and Fon-Der-Flaass.
- The quotation that general-m analysis "seems intractable" (source p.3) concerns cataloguing all orbits, not typical ones, so it is weak evidence that this conjecture was hard.

## The five adversarial questions

1. Section 4.1. Stated as proved: the count C_m binom(n-2m+1,2m) of good ICS and its asymptotic, with a short justification. Conditional: "if one could show that all such elements belong to orbits of size m+n+1, and one could show" the total is asymptotic to n^(2m)/(m!(m+1)!), "that would be sufficient". Hoped: "One should be able to extract the latter (enumerative) piece from the formulas in [12]"; "possible in principle". Left open: the orbit claim. The proposal is a completion of that named plan: same good-family shape, same comparison. It does the one step left open, with two changes: a larger gap so that at most one mark is hidden, and removal of symmetric sets. The enumeration is elementary and does not need [12]. So it completes the outlined plan, and the completion is real work, but Route C shows that work is not needed.

2. Theorem 1.1. Used correctly; bracketing confirmed on p.4 and against the proof's sets D and C. It is needed only as the one-step formula L3. It could be replaced by direct row-by-row toggling, which I checked only in three hand cases, not in general. m=1 is correct, with N=n+2. Small n only affects constants. The claim about the source wording is correct: at m=1, n=6, the good set [1,3] has orbit [1,3],[2,4],[3,5],[4,6] of size 4, not 8, and generally length n/2 for even n>=6. That is a wording defect in a conditional sentence and earns no credit. I did not determine whether good sets with small gaps fail for other reasons.

3. General theory. Yes, as stated above, through Theorem C. Inputs read: SW Theorems 7.5, 7.7, 7.8 and Definition 7.6; DPS Lemma 2.1, Theorems 3.2, 4.1, 4.4, Corollary 4.5. No follow-up to 2505.04000 proving 4.1 was found. I did not find interval-closed-set homomesy or toggle-group results implying it. The bounded search did not target the conjugacy itself, MathSciNet, zbMATH or citation indexes.

4. Short generic argument. Yes: Theorem D, about one page beyond the one-step formula the author also needs.

5. Family. All 57 accepted and 39 prior scopes displayed and compared. Nearest neighbours are 338887 (rotor networks), 345545 (stack sorting), 347230 (interval transform on posets), 359279 (tableau minors). None concerns rowmotion, toggles, interval-closed sets or plane partitions. Displays cut statements at 190-250 characters, so this is bounded. Keyword scan over full records: only 'poset' in 347230.

## Strongest case for credit

- A deliberate printed 2025 conjecture is proved in full for every m, with a rate r(n)=1-O_m(1/n), and no earlier proof was found.
- Theorem C is not in anything read. A coauthor of the source, Striker, also coauthored both SW and DPS, and the source still calls the conjecture experimental and offers only a conditional plan. That is real evidence the link was not obvious.
- Interval-closed rowmotion differs from order-ideal rowmotion in general: the n+5 and quadratic orbits exist, and the extra Inc term must be shown to fit exactly.
- The campaign rule says shortness and familiar tools do not establish routineness.

## Strongest case against credit

- The complete bridge exists and is written out: every hypothesis and conclusion is paid, from actually read primary statements (rule satisfied; not snippet similarity).
- The value m+n+1 is exactly the classical order a+b+c-1 at c=2. The phenomenon the conjecture asks about is the 1995 theorem, transported.
- The noncrossing rotation that is the author's main mechanism is already printed for [2]x[m]x[n].
- The source named the plan, and the only input beyond the classical theorem is a one-step set computation that the author also needs.
- Direct precedents: 336276 was excluded after a second qualification found a short generic route making the original proof unnecessary, and 341690, 328851 and 322479 were excluded on complete bridges to earlier theorems.

## Why not PARK

No specific unread proof blocks the decision, and the ordinary proof is complete. The unread items (Cameron and Fon-Der-Flaass 1995, Pechenik 2014) are attributed inputs whose statements are verified through two papers that re-prove or cite them. A PARK would only defer the same judgment.

## Limits

- Theorem C and Theorem D are reviewer-authored and have not been independently reviewed. Root may want them checked before relying on the exclusion.
- DPS's proof of its Theorem 3.2 relies on a stated extension of [Pe14] to non-full content; SW gives a separate proof. Upstream results were not audited.
- SW prints m+1 blocks where its word convention gives n+1; Theorem D avoids this.
- The addendum's consistency remark about n+5 orbits is only a sanity observation: p.39 lists single-chain representatives for those orbits, and I did not check every orbit.
- Conjugacy search coverage is two native queries in total.

## Formal assessment (dormant, no dispatch recommended)

Literal endpoint: for every m>=1,
Tendsto (fun n => (card {I : ICS (Fin m x Fin n) | Function.minimalPeriod Row I = m+n+1} : Q) / card (ICS (Fin m x Fin n))) atTop (nhds 1),
with ICS the convex subsets for the product order and Row the composition of literal toggles in reverse linear-extension order. minimalPeriod matches orbit size because Row is a permutation. The author's plan is sound: avoid importing Theorem 1.1, whose own proof rests on [ELMSW, Thm 2.20], and prove the transitions by toggles. Two additions: fidelity needs either independence of the linear extension or a fixed extension justified against source Definition 1.9, and the toggle proof must handle transient empty rows, which arise at the flip (row k empties and refills). If this were ever formalized, Route R is the feasible path; Route C would require formalizing the plane-partition theorems.

## Process disclosures

- Bootstrap and verify_frozen before ran first, as ordered. TASK.txt read in one chunk 0-12147 and inherited-denials.json in 21 contiguous chunks 0-309136.
- Denials chunks 07-10 were piped through head -c 15500 outside the runner; the cut fell in the echoed receipt, not the data. Those four shell exit statuses are head's; the lane receipts record the runner's true exit.
- scopes-c2 and scopes-c3 exited 1 with KeyError because accepted rows 56-57 have no statement field. Receipts retained; repaired by scopes-repair, not rerun unchanged.
- PROOF.md was written before inputs/author-candidate.md was opened. The route itself was disclosed by the task.
- Search: 2 of 2 calls, 2 of 6 strings (the native tool takes one query per call), each precharged, each full response saved in the next tool call. GET: 3 of 6 hops, all HTTP 200, no redirects, no denials touched.
- Protected peers not accessed. No new denials. Native, transient and writer peaks unknown; no universal cap claim.
