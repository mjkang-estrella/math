# REVIEW: MathDB 342017, smooth arithmetical structures on P_{m,n}

Reviewer: Claude Opus 5.5, personally, no children. Credit 0; campaign 58/80 unchanged.
Root alone adjudicates. Independent reconstruction: PROOF.md (saved before the author file was opened).

## Recommendation: EXCLUDE AS ROUTINE OR CORRECTION (moderate confidence)

The mathematics is correct and I found no gap. I recommend exclusion on significance only:
the literal statement, read as it must be read, has a complete one-page proof from the
source's own Lemma 2.7 plus six one-line identities (PROOF.md section 7). This is a
judgment call. It is NOT a prior-art finding: I found no earlier proof.

If the user or root overrules, the only defensible credit unit is the all-m exact theorem
(quasi-polynomial, limit alpha_{m-1}), not the bare growth statement.

## The five adversarial questions

### 1. Literal
Conjecture 1.4 (visually read, p2): "grows at the same rate as binom(m+n-1,n)". The sentence
immediately before says each proved case "grows on the order of a polynomial of degree m-1 in n".
So the literal is N(m,n)=Theta_m(binom(m+n-1,n)) for fixed m, n->oo.
- Ratio tending to 1 is false at m=1 (limit 4). So "same rate" cannot mean asymptotic equivalence.
- Uniform two-variable reading is false, and the author is right. N is symmetric, N(m,1)=4 for m>=3,
  while binom(m,1)=m. The author's n=2 example N(m,2)~(37/4)m against m^2/2 is also correct.
- The constant goes beyond the literal. The literal asks for no constant, no quasi-polynomiality
  and no generating function. "Same rate" is informal, so root should still rule on the binding.

### 2. Is the bare growth routine? Yes in substance, with a stated limit.
- Lower bound N(m,n)>=binom(m+n-2,m-1): three lines from source Lemma 2.7. (a,b)->(a,b+2a) raises n by 1
  and fixes m; (a,b)->(a+2b,b) raises m by 1 and fixes n; start at (1,1).
- Upper bound N(m,n)<=C_m n^{m-1}: about ten lines from the two 2-state doubling machines: at most m
  L-runs, at most 2m-1 letters R, and A strictly monotone in a run length in steps of 2.
- Lemma 2.7 IS the Stern-Brocot letter rule, so the reformulation is a restatement of a source lemma.
  The source's F(4a,b) reductions are instances of the same commutations.
- Limit: I did NOT carry out a literal iteration of the Table 2 casework for general m. I began a shape
  closure (F(4s,ds-s'), F(2s,ds-2s'), F(s,ds-4s') with boundary cases) and did not finish it. The source
  never states such a closure. What is complete is the one-page proof, which replaces the casework.
  So "routine iteration of the source's cases" is accurate in spirit, not as a completed derivation.
- Exact constant: it does not change the answer for the literal. It is a separate, stronger theorem. It needs
  the coupling of both machines, the block-graph recursion and the pole comparison. It is correct and
  more substantial, but it answers a question the record does not ask. Compare the 344875 precedent.

### 3. Transducer, automaton, poles, source agreement, Table 2
All checked by hand; no program was used.
- Author's B1, B2: correct. All ten rows of B3 match my independently derived table after swapping L/R
  and x/y (author rho=b/a is my 1/x). Map: S=00, P=10, Q=01, P'=21, Q'=12, T=22, U=30, V=03, W=23, X=32.
- B4: I re-derived all four reduced equations from B3. Correct. B5 recursions: correct, including t_{k-4}.
- Order bounds: at x=1 order k+1; at -1,+-i order <=ceil(k/2)<k+1. Both independently derived.
  alpha_0=4, alpha_1=37/4, alpha_k=2alpha_{k-1}+(5/4)alpha_{k-2}.
- The author's a_2 numerator 4+9y+18y^2+16y^3+20y^4+12y^5+9y^6+4y^7+y^8+y^9 equals my own
  expansion coefficient by coefficient.
- Source agreement: m=1 exact (Thm 3.1), m=2 exact including small n (Thm 4.2). Spot checks against
  Table 1: n=5:34, n=10:80, n=15:127. m=3 limit 47/4 n^2 agrees.
- Table 2 error CONFIRMED and located independently. Rows k=0 mod 4, t=2 and t=3 mod 4 use a reduction
  needing t>=4. True: t=2 gives n-5, t=3 gives n-7, not n-6 and n-8 (visually read, p10).
  The source formula's generating function differs from ours by exactly -x^4/(1-x^2): one too few for every
  odd n>=5. Witness (a;b)=(3,2,1;5,4,3,2,1) on P_{3,5}, so N(3,5)=166, printed 165; N(3,7)=377,
  printed 376. Theorem 5.3's constants for odd n and the Theorem 1.5 P_{3,n} constant inherit this. Zero credit.
- Not checked: the author's statement that Table 1 was compared through n=15 beyond my three spot checks.
  The author's Table 3 limit is honest (no brute force was run; neither did I).

### 4. Later work and the final
Two searches, two strings (search-response-1.txt, -2.txt). Neither surfaced a proof or refutation for
general m, and neither surfaced any paper using Stern-Brocot or transducers here. Search is navigation only.
- Keyes-Reiter 2007.15100v2: mentions the conjecture in one sentence of the introduction (p1) and cites
  the arXiv version only. No proof, no status. Its paraphrase says "#A(G)", loosely; the conjecture is about smooth structures.
- Glass-Kaplan 1908.04395v1 (fetched, 1 GET): Theorem 21(3) restates m=1 only and says that in general
  "it appears to be quite difficult to count precisely the number of smooth arithmetical structures".
  It also reports only cubic bounds for bidents. No general-m result.
- Integers final (the search summary gives Integers 20 (2020) A68): UNREAD. The core.ac.uk artifact is closed. A
  cupola.gettysburg.edu record, ar5iv and the unversioned arXiv URL also appeared; I requested none of
  them because they would be alternate routes to that closed work.
- What that leaves open: whether the final changed or withdrew the conjecture, corrected Table 2 or Theorem 5.3,
  or added general-m results. It cannot affect the mathematics of the theorem as stated from v1.
- Not covered: MathSciNet, zbMATH, citation indexes, the four closed registry roots, Raney's 1973 paper
  (unread; PROOF.md proves the six identities directly and does not rely on it). No worldwide novelty claim.

### 5. Family comparison
I compared all 96 supplied entries using extracted title, tags and scope or the first 90 characters of the statement,
plus a keyword scan of both full files (arithmetical, Stern, Brocot, continued fraction, transducer,
quasi-polynomial, doubled edge, Catalan: all zero hits). Bounded non-overlap. Nearest by words only:
352253 (doubled 3-regular graphs, unrelated meaning), 345545 (growth constant, different object). This is a
truncated-field comparison, not a full reading of every statement.

## Strongest cases

For credit:
- A deliberately posed conjecture, settled for every m, in a stronger exact form, with a closed-form constant
  whose eigenvalues 5/2 and -1/2 are nowhere predicted in the source.
- The source says a direct approach "seems out of reach" and needs a 28-row table for m=3; that table contains an
  error, which shows the casework was not mechanical. The source's co-author later calls smooth counting difficult in general.
- No published theorem yields the result. Raney-type transducers give rationality at best.
- No earlier proof found.

For exclusion:
- The literal asks only for Theta for fixed m, and that has a one-page proof from source Lemma 2.7 and six identities.
- The lower bound is a three-line corollary of a printed source lemma and already gives the binomial shape.
- No new invariant is needed for the literal: the L-count is Lemma 2.7 restated, and the upper bound is a run count.
- The source's "out of reach" remark concerns inverting F exactly, not growth.
- The exact constant answers more than was asked, and campaign rules give no credit for parameter or constant strengthenings as such.
- The author's own review concedes the Theta reading may fairly be called iterated casework.

## Gates

| Gate | Result |
|---|---|
| Literal | PASS on fixed-m Theta; root ruling needed because "same rate" is informal |
| Original source | PASS (v1 fully extracted; pp 2,4,5,10 visually inspected) |
| Final or correction | HOLD: Integers final unread and closed |
| Ordinary proof | PASS (independent reconstruction; author audited, no gap) |
| Prior art | Bounded: no match in 2 searches, 1 survey, 1 citing paper |
| Novelty | Not established beyond that bounded search |
| Significance | Recommended FAIL on the literal (routine); judgment call |
| Family | PASS, bounded non-overlap with 57+39 |
| Formal | Not run; plan assessed below; dormant |
| Process | See disclosures |
| Acceptance | Root only. Credit 0 |

## Formal plan assessment (dormant; no dispatch recommended)

The author's plan is feasible. Literal Lean endpoint if root ever revives this:
for all m>=1, there exist 0<c<=C and n0 such that for all n>=n0,
c*binom(m+n-1,n) <= (SArith m n).ncard <= C*binom(m+n-1,n), together with Set.Finite (SArith m n).
State finiteness explicitly because ncard of an infinite set is 0. Sharper, separate: Tendsto of the ratio to alpha_{m-1}.
SArith must use labels on Fin m and Fin n exactly as Definitions 1.1-1.3: gcd of ALL labels 1, a_1 | a_2+2b_1,
the m=1 and n=1 boundaries a_1 | 2b_1 and b_1 | 2a_1, a_m | a_{m-1}, strict decrease.
Source Definition 1.1 says "nonnegative": keep that and prove positivity, as in PROOF.md section 0.
Controls must use N(3,5)=166, not the printed 165. The plan's explicit-bounds route avoids partial fractions and is sensible.

## Disclosures

- write_lane.py was invoked directly from the shell, as an authored-write helper, not under run.py.
- pdftotext and pdftoppm wrote work/*.txt and work/render/*.png from inside runner children, as PDF processing;
  the runner child also created work/ and work/render/ directly.
- Native Read presented four rendered PNGs: gw-02, gw-04, gw-05, gw-10. gw-01 was rendered, not viewed.
- scopes_compact_57 exited 1 with a documentary KeyError; receipt retained; repaired as scopes_compact_57_repair.
- Keyes-Reiter was read for its mentions and first page, not in full. Glass-Kaplan was read at its matching passages only.
- Resource figures are sampled by the runner; native, transient and writer peaks are unknown.
