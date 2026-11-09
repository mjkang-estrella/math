# REVIEW.md - independent adversarial qualification of MathDB 347063

Reviewer: Claude Opus 5.5, high effort, working personally. No children, Lean, or mathematical
programs. Credit 0; campaign 58/80 unchanged. Root alone adjudicates.

## Bottom line
- Part (a), Split Smallest = phi^2 n + O(log^2 n), is PUBLIC. Exclude it. Cusenza et al., Bounds
  on Zeckendorf Games (arXiv 20 Sep 2020; Fibonacci Quart. 60(1) (2022) 57-71), prints the exact
  length identity for every game and says this conjecture "has been shown here".
- Part (b), Combine Smallest = c n + O(sqrt n log n), c = 5/2 - phi + sum_{j>=2} 1/F_{2j}
  = 1.2064812 (hand value), survives. I reconstructed it, the author's proof is correct, and I
  could not exclude it. No prior proof was located within a small bounded search.
- The record's literal is defective. Read as written the game has zero moves.
- RECOMMENDATION: CREDITABLE SUBJECT TO LEAN AND PAPER, narrowed to part (b), with part (a)
  attributed and uncredited. Significance is modest and my confidence in it is only moderate.

## 1. Literal gate
Record: "A Zeckendorf game starts from the Zeckendorf decomposition of n". Source Definition 1.1
(arXiv v1 p1, viewed; final p152-153): "At the beginning of the game, there is an unordered list of
n 1's. ... therefore the initial list is {F_1^n}." From the Zeckendorf decomposition no move is
legal, so the literal game has 0 moves and neither clause holds. That reading is a transcription
error by the record, not a claim of the source; the record's own citation and its phrase "the
paper presents these claims" fix the intended object.
Verdict: LITERAL AS WRITTEN FAILS; SOURCE BINDING PASSES. A proof for the source game resolves the
record's intended problem but not its words. Noting the error earns nothing. Root should decide
whether the campaign's "exact scope" wording admits a source-bound endpoint; prior39 item 31
(MathDB 325512) is a precedent for binding to the source when the record differs.

Source text quoted exactly:
- Definition 1.1 moves: "(1) If the list contains two consecutive Fibonacci numbers, F_{i-1}, F_i,
  then a player can change these to F_{i+1}. ... (2) If the list has two of the same Fibonacci number,
  F_i, F_i, then (a) if i = 1, a player can change F_1, F_1 to F_2 ..., (b) if i = 2, a player can
  change F_2, F_2 to F_1, F_3 ..., and (c) if i >= 3, a player can change F_i, F_i to F_{i-2}, F_{i+1}".
- Theorem 1.2: "The number of moves in the longest game is bounded by 3n-3Z(n)-IZ(n)+1, where Z(n) is
  the number of terms in the Zeckendorf decomposition of n and IZ(n) is the sum of indices in n's
  Zeckendorf decomposition. As the number of moves is at least n - Z(n), each game takes order n moves
  to play."
- Conjecture 1.4: "For Split Smallest, the number of moves grows linearly with n; numerically the
  constant appears to be the golden mean squared. For Combine Smallest games, the number of moves grows
  linearly with n, with the constant appearing to be approximately 1.206."
Theorem 1.2 already gives Theta(n), so "grows linearly" alone is source-own. The content is the
existence of the limits and their values: limit phi^2, and a limit near 1.206. An exact c meets
"approximately 1.206" (it rounds to 1.206) and supplies more than was asked. Final text: Conjecture 1.4
is unchanged at FQ 58(5) printed p154 (viewed).

## 2. Mathematics
Files: PROOF.md (written before opening the author) and PROOF-ERRATUM.md (operative correction).
(a) PASS. Weights w_i = i+2+(1/phi)(-1/phi)^i drop exactly 1 on C_1 and every split and exactly k on
C_k, k>=2. Hence length = phi^2 n - W(n) - sum_{k>=2}(k-1) MC_k for every game. In SS a combine C_k,
k>=2 occurs only at a position with at most imax chips, giving the O(log^2 n) error.
(b) PASS, by independent reconstruction.
 - Priority evaluation: from a pool state B_p(r,m,M) the S_p step and its relaxation are forced.
 - Rotation: the low state is the integer r in [0,F_{p-1}), r -> r+F_{p-2} mod F_{p-1}, one cycle
   because consecutive F's are coprime. My recursive Insert lemma matches the author's ADD descent.
 - Chip balance: F_{p+2} pool chips -> F_p chips at p+2, splits F_{p-1}+(F_{p-2}-1)=F_p-1, moves
   F_{p+2}-1 per cycle. Two routes agree: my A(q)=F_q-1 recursion and the author's d_q/e_q balance.
 - Assembly: mass conservation gives m_p = n/F_p+O(1) at every level, so errors do not accumulate;
   level p contributes m_p(1-1/F_{p+2})+O(F_p); truncate at F_{P+2}<=sqrt n; the remainder is bounded by
   the potential or the author's Lemma T.
 - Endgame: this is where I first went wrong; see section 3.
 Constant: sum over even p>=2 of 1/(F_pF_{p+2}) telescopes to 1/phi-1/2 through
 F_{p+1}F_p-F_{p-1}F_{p+2}=1. Hand value c=1.2064812.
 External consistency only, not evidence of proof: source Fig. 2 fits 1.20647n, and c-1.20647 times
 1.6*10^6 is about 18, inside the error term.

## 3. Audit of the author
Author proof of (a) and (b): correct. Their endgame list is RIGHT and my first draft was WRONG on one
entry. For K=3 with a repeat at p-2 (Case 3), combines outrank splits, so (p,p+1) fires before S_{p-2}
and the chip at p-1 is not absorbed: READY(p+2; O+1, ...), not O-4. I found this only by comparing
with the author. It shows that this list is the delicate part and must be split by Case 1, 2, 3 in any
formal proof. PROOF-ERRATUM.md has the corrected table. The final conclusion did not change.
Minor author items: A5.4 "transcendentally unusual" is loose and unused. A6 admits no prior-art check;
this review supplies one and it changes the status of (a). A0's scope warning is correct.

## 4. The adversarial questions
1. Prior art. Two search strings, six GET hops, no failures.
   - FQ final found and compared with arXiv v1 sentence by sentence: Conjecture 1.4 retained; (3.14)
     coefficient repaired to 2MC_1+MC_2.
   - Applicable result found: Cusenza et al. Theorem 1.3 and (3.16), printed p59 and p67, viewed:
     length = sum a_j delta_j - MC_2 - 2MC_3 - ... with a_j=F_{j+2}-j-2. Since phi^2 F_j - w_j = a_j,
     this is exactly my identity (II). Their p59 sentence claims the Split Smallest constant. Their text
     gives only the upper bound explicitly; the matching lower bound is the three-line chip count in my
     section 2. Complete bridge supplied, so (a) is public plus a routine completion.
   - Combine Smallest: nothing in Cusenza et al. (the phrase does not occur), the 2025 Cheigh et al.
     (no occurrence; reference list only), The Bergman Game (none), or the 2025 Williams slides (lists CS,
     no length result). Their future-work text says tightening needs "quantifying the number of each
     combining moves", which is beyond scope there.
   - NOT covered: MathSciNet, zbMATH, Google Scholar citation lists, the two original game papers,
     the rewriting and numeration literature, and anything phrased without "Combine Smallest".
2. Is (a) routine? It is short and the identity is public, so yes, and it does not need a routineness
   ruling: it is excluded as public. Against the source alone (a) was not implied: the three source
   relations leave MS_3 free; the missing relation is the conjugate functional, which Cusenza et al.
   obtained by matrix inversion.
3. Is (b) routine? I tried and failed to reduce it.
   - Potential: unit drop on all combines forces w=alpha F+1, whose split drop is 0, so no linear
     functional works. I checked this; the author's claim holds, even restricted to moves CS uses.
   - Reduction to (3.16): CS needs sum (k-1)MC_k = (phi^2-c)n, i.e. the individual combine counts, which
     (3.16) leaves free. The chip-balance system has about imax equations in about 1.5 imax unknowns even
     after discarding odd splits, so it is underdetermined.
   - Source: Theorem 1.3's one-state invariant does not extend; Theorem 1.2 gives only Theta(n).
   - Generic renormalization: I found no route that bypasses the level dynamics.
   No complete routine bridge exists to my knowledge. That is not proof that none exists.
4. Would a specialist learn something? From (a): nothing beyond 2020. From (b): that CS renormalizes
   level by level with an integer rotation mod a Fibonacci number, that only even-index splits occur in
   the low cascade, and that the constant is a closed form with an odd-indexed reciprocal Fibonacci
   sum, where the source only fit 1.20647. That is a real but modest finding about one algorithm. A
   specialist tracing the process might expect the pool pattern; the exact constant and endgame are
   not free. (b) alone is the only part that can qualify.
5. Family: all 96 supplied scopes compared (family-comparison.md), bounded nonoverlap; nearest is a
   rotor-network count, 338887.

## 5. Strongest cases
FOR: A deliberate printed conjecture half that a Fibonacci Quarterly follow-up left unaddressed since
2020, resolved in full with an exact constant and no reduction to a prior theorem. It is not a
correction, parameter instance or potential calculation. The proof needs a real structural step and a
delicate endgame, which caught this reviewer out.
AGAINST: It is a bookkeeping analysis of one deterministic algorithm, from an undergraduate-research
paper, using elementary tools, and half of the stated conjecture is public. The record's words are
wrong. The error term O(sqrt n log n) is much weaker than the data, whose spread near n=1.6*10^6 is
about 10, so the structure of the error is not understood. Under the interval precedent (336276), a
first favourable qualification has been overturned before by a generic proof; I looked for one and did
not find one, which does not exclude it. The search was small.

## 6. Recommendation
CREDITABLE SUBJECT TO LEAN AND PAPER, narrowed to part (b) with part (a) attributed and uncredited.
Reasons: the mathematics is correct; no applicable theorem or complete routine reduction for (b) was
found after a real attempt; no specific unread applicable proof is identified, so no HOLD is justified;
the literal defect is an unambiguous record error. Confidence on significance is moderate, not high.
Root should treat the literal-binding question as its own decision, and the user may reasonably hold
the bar higher for a single-algorithm move count.

## 7. Formal assessment (dormant, no Lean run, no dispatch)
The author's plan is sound in outline. Endpoint I would require:
 - Positions finitely supported on Nat; the literal Definition 1.1 move relation; SS and CS as actual
   deterministic priority step functions; length to the terminal position.
 - Start n e_1, stated openly as the source game, with a short docstring that the record's wording
   would give zero moves. Optionally a control lemma for that, zero credit.
 - (b): exists C, for all n>=2, |CS n - c n| <= C sqrt n log n, with c a tsum, plus the closed form and
   a rigorous bracket such as 1.206 < c < 1.207. (a) may be included with attribution, but earns nothing.
Cautions: the endgame must be split by K and by Case 1/2/3 (see the erratum); the F_0 := 1 convention
hides a p=2 special case; Mathlib's Nat.zeckendorf uses the standard index shift; the integer weight
i+3 does not bound the tail because S_2 then drops 0, so use Lemma T or the real potential.

## 8. Gates (details in review.json)
literal: FAIL as written / PASS source-bound. original source: PASS. final/correction: PASS.
ordinary: (a) PASS, (b) PASS. prior: (a) PUBLIC, (b) none located, bounded. novelty: bounded only.
significance: (a) none, (b) modest. family: bounded nonoverlap. formal: unpaid, dormant. process: PASS
with the disclosures below. acceptance: root only, credit 0.

## 9. Disclosures
- PROOF.md first contained the endgame error above. It was kept unedited; the erratum corrects it.
- Receipt scopes_accepted_c2 exited 1 (KeyError on rows lacking statement). Retained, repaired by
  scopes_accepted_c2_repair.
- The first accepted-scope display exceeded the tool limit and the harness saved a copy outside the
  lane, in the session tool-results folder. I did not open it. The same text is in the lane receipt
  output, and I re-read the scopes through the runner in smaller chunks.
- Scope statements were read truncated, as stated in family-comparison.md. Accepted result 58 is not
  in the supplied scopes.
- Six own rendered PNG pages were viewed with the native reader, as authorized.
- Document processing used pdftotext, pdftoppm and a text diff. No mathematical program or enumeration
  ran; all arithmetic is by hand.
- Search answers are navigation only and every cited claim was read in a primary PDF.
- Unknown native, transient, writer and supervisor resource peaks are not claimed.
- The ordinary proof has been checked by two readers (author, reviewer) and no machine.
