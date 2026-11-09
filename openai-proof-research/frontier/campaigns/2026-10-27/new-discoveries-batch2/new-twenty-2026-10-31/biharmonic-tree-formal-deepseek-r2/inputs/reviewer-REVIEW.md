# REVIEW.md - independent adversarial qualification of MathDB 352303

Reviewer: Claude Opus 5.5, high effort, no subagents, no Lean or formal tools, no CAS or numerical programs.
Credit 0. Campaign 58/80 unchanged. Root alone adjudicates.

## Recommendation

**CREDITABLE SUBJECT TO LEAN AND PAPER**, with low-to-moderate confidence and modest significance.

I tried to exclude this and could not do so under the campaign's stated standard. No published theorem I could read gives the
result, the coefficient and majorization routes genuinely fail, and no reduction to the source's own argument exists. But the proof is
short, it follows the classical Wiener-index template, and the prior-art search was thin (two query strings). This is a judgment call that
root or the user may reasonably decide the other way. See "Strongest cases" and "What would change this".

One cheap step should come before any Lean spend: a citing-work check of the published paper, DOI 10.3934/math.2022337.

## 1. The ordinary mathematics: PASS

PROOF.md was written and sealed in the lane before inputs/author-candidate.md was opened. Only the one-line mechanism in TASK.txt was
known. It proves the full statement by the edge-pair formula and a whole-path merge, with the exact symmetric identity

    N(T')-N(T) = (r-1)(pq/3)[ r(2p^2+2q^2+3pq+3p+3q+2) + 2pq(p+q) + 3pq + p + q ] + 2S pq(p+q+1).

### Audit of the author (read only after PROOF.md existed)

B1 formula: correct, same X = B M^{-1} argument. I rechecked <x_e,x_f>: with outer sizes a,b and middle c, the sum is
(ab/n^2)(-(n-a)-(n-b)+c) = -ab/n, since 2n-a-b-c=n.

B2 lower bound: correct, termwise, identical to mine.

B2 upper bound: correct. The author uses a different and simpler shift, moving one vertex so (p,q) becomes (P,q-1), P=p+1, t=r-1, n=P+q+t.
TASK question 2 asks for this identity in full. By hand, starting from the author's decomposition:

    N(T')-N(T) = 2S(P^2-q^2) + E,  E = (q+t)^2 U(P) - (P+t)^2 U(q) + 2P^2 Phi(q-1) - 2q^2 Phi(P-1).

The S term comes from Phi(P)+Phi(q-1)-Phi(P-1)-Phi(q) = P^2-q^2. The Phi product term comes from
Phi(P)Phi(q-1)-Phi(P-1)Phi(q) = P^2 Phi(q-1) - q^2 Phi(P-1). Expanding E in t, with U(k)=k^2+2Phi(k-1)=k(2k^2+1)/3:

* t^2: U(P)-U(q).
* t^1: 2qU(P)-2PU(q) = (2Pq/3)(2P^2-2q^2) = (4/3)Pq(P^2-q^2).
* t^0: q^2 P^2 + 2q^2 Phi(P-1) - P^2 q^2 - 2P^2 Phi(q-1) + 2P^2 Phi(q-1) - 2q^2 Phi(P-1) = 0.

So N(T')-N(T) = (P^2-q^2)(2S+(4/3)tPq) + t^2(U(P)-U(q)), exactly as claimed. It is strictly positive because P>q>=1, t>=1 and U is strictly
increasing. The case q=1 is covered (Phi(0)=0, the branch disappears). Rooting at a leaf gives a parent, so a degree >=3 vertex at maximum depth
has at least two descending pendant paths and r>=2. Both proofs reach the same theorem by different shifts, and each was checked by hand.

Formula against the source, by hand (TASK question 2): double star S(a,b) gives BH = n^2-2n+4ab+(ab+1)^2/n, exactly source Theorem 5.1 (viewed, p.9).
I also checked the firefly family F_{0,t,n-2t-1}, which gives exactly the second display in the proof of Theorem 5.5(3), and P_4, P_5, and three shift instances
computed from the formula directly (see PROOF.md).

Minor documentary points, none affecting validity. The author writes c_{n-3} for the coefficient I call c_3 (a different indexing convention). The author says the
published final is unread and that arXiv shows no journal reference; the final does exist and I read it (below). PROOF.md Remark 2 has a stray fragment
"c_{n-1}..." in its first line, left as written so the pre-author file stays intact; the intended statement is c_2=W and c_3 as given there.

## 2. The adversarial questions

**Q1. Is it routine: does a known monotonicity, majorization or shift theorem give it?** Not that I could establish.

* Coefficients (Mohar; Csikvari), recalled from memory, bodies not read. The author's claim checks out: by Vieta, BH(T) = W(T)^2/n - 2 c_3(T), with c_2=W and c_3 the next
  Laplacian coefficient. This form is confirmed by hand on K_{1,3} (81/4-12) and P_4 (25-12). At n=5 the star has W=16, c_3=18 and the path W=20, c_3=21: both rise, one is subtracted.
  Any coefficient-monotone statement therefore gives neither inequality alone. Both bounds need a quantitative comparison of the two changes.
* Majorization and Schur-convexity: a clean nonmatch for every n>=5. The nonzero spectra of star and path are not comparable. First partial sum: star n > lambda_max(P_n), since
  lambda_max(P_n)<4<n. Partial sum of the top n-2: star 2n-3 < 2n-2-lambda_2(P_n), since lambda_2(P_n)=2-2cos(pi/n)<1 for n>=5 (n=5 explicit: 5 vs 3.618 at k=1, 7 vs 7.618 at k=3).
  So no sum-preserving majorization chain from star to path exists.
* Not excluded: weak majorization of the reciprocal spectra, which would give all convex increasing functions of 1/lambda at once. I could not prove or refute it and know of no theorem stating it.
* A pointwise domination shortcut does not come from this shift: for p=q=2, t=1, the affected entries change from {4,4,2} to {6,3,3}, so the sorted lists are not comparable termwise even though the sum of squares rises from 36 to 54.
* Reduction to the source: none. Lin's proofs use characteristic polynomials of special families (Thm 5.1, 5.5) and eigenvalue estimates (Lemmas 2.7, 2.8 in Thm 5.2). The pair formula and the shift are not in the source.

**The honest counterweight.** The architecture is the classical Wiener proof one level up. There W = sum a(n-a), the star bound is termwise, and the same one-vertex shift gives delta W = (P-q)t. Here the first-level edge sum is replaced by an
edge-pair sum and the same steps go through, the t^0 term cancelling automatically because at t=0 the two shapes are the same path. The edge-pair formula is also a one-line consequence of classical
data: with Kelmans' forest count c_3 = sum a m d (recalled, not read), the identity a(n-a)d(n-d) - n a m d = a^2 d^2 turns BH=W^2/n-2c_3 into N/n. No obstacle appears at any point; my merge works with no relation between p and q.
This is a template and not a theorem. Its hypotheses do not imply the target, since the second-order identity is a fresh calculation, so it does not meet the campaign's requirement of an actual primary theorem plus a complete reduction. I report it as the strongest objection and not as an exclusion.

**Q3. Prior proofs (bounded).** None found. Details in section 3.

**Q4. One-parameter family.** Spectral family sum lambda^{-k}: k=1 is the classical Kirchhoff/Wiener case, k=2 is the target, and the proof does not reach k>=3, because M^{-1} has mixed signs (comparable edges positive, incomparable negative when oriented from a root) so tr M^{-3} has no termwise form.
Abstract family N_alpha = sum w(e,f)^alpha: the t^0 cancellation holds for every alpha (checked), alpha=1 gives exactly t(P^2-q^2) for the path part, and integer alpha plausibly follows the same way; I did not prove the family. Only alpha=2 is spectral. Since it is a reviewer-made non-spectral family with
no known members beyond this, I do not think the target is a "parameter instance" in the campaign's sense, but the ease of the family is further evidence that alpha=2 is not special inside the shift.

**Q5. Family comparison.** All 96 supplied scopes were extracted and compared (57 accepted, 39 prior). No overlap. The nearest are 349441 (hubs-biased Kirchhoff-index ordering on general graphs, a different invariant and statement), 330264 (cospectrality of trees and Coxeter growth), prior result 15 / 372758 (connection-Dirac spectral dominance),
prior result 36 (a Steiner distance tensor on a star) and 354228 and 365710 (tree labelling, irregularity). None concerns reciprocal Laplacian moments of trees or the same extremal question. Limitation: the 58th accepted result, 382297, is not in the supplied file of 57; from the campaign records it is a bunkbed result and unrelated.

## 3. Source and prior-art findings

* Literal: inputs/literal352303.json and the raw JSONL. Source Conjecture 5.3 (arXiv v1, p.10, viewed): T_n a tree on n>=5 vertices, both inequalities, both equality clauses. Exact match. "BH" comes from the source abstract and p.2.
* Final version: **new finding not available to the author.** Z. Lin, The biharmonic index of connected graphs, AIMS Mathematics 7(4) (2022) 6050-6065, DOI 10.3934/math.2022337, received 19 October 2021, revised 7 January 2022, published 17 January 2022, is the published form. Conjecture 5.3 is retained verbatim on p.6058 (viewed), with Theorems 5.1, 5.2 and 5.4 around it. So the conjecture survived peer revision and the final paper does not solve it. I read the abstract, introduction fragment, Section 5 through Theorem 5.4 and the start of the bibliography, not the whole paper.
* Wei, Li, Yang, Biharmonic distance of graphs, arXiv 2110.02656v2 (7 Sep 2022): Problem 6.3 (p.20, viewed) asks for bounds on B(T) for trees of given order and the extremal graphs. It contains no star, path or tree extremal theorem, and v2 postdates the conjecture and leaves the problem open. Its Remark 4.1 points to the sum-of-powers literature.
* Yi, Yang, Zhang, Patterson, arXiv 1709.02790v2: performance measures for named graphs; the word "tree" occurs only in a citation and the bibliography. Theorem-level nonmatch.
* Two searches, one query string each (budget 2 calls, 6 strings): neither surfaced a proof. Search is navigation only and is not novelty evidence.
* MATCH 91(2) 285-286, surfaced by search 1, timed out at the guard after 20 s (true exit 1). Its identity and content are unread, the work is closed with no retry, and it is not treated as a hold, since nothing indicates relevance beyond a search hit.

Not covered, stated precisely: MathSciNet, zbMATH, Google Scholar or any citing-work index; papers citing AIMS 2022 or 2110.02656 after 2022; the journal version of Yi et al. (IEEE Trans. Inf. Theory 2022), which search 2 listed only through third-party index URLs and which I did not attempt to fetch;
the sum-of-powers papers named by WLY: Zhou LAA 429 (2008), Liu-Liu AML 24 (2011), Das-Xu-Liu LAA 439 (2013), Chen-Das DM 338 (2015) (all unread; WLY describes them as bounds for graphs by parameters, and leaves the tree problem open after citing them, so they are not specific applicable proofs and I do not hold on them); Mohar's and Csikvari's papers and Kelmans's formula (from memory only).
This is not a worldwide novelty claim. A problem this accessible, posed in 2021-22, could easily have been solved in a paper these two strings missed.

## 4. Strongest cases

**For credit.** A deliberate conjecture, stated in a peer-reviewed paper and retained through revision, concretizing an explicitly open problem that was still open in the companion's 2022 version. The source reached only double stars, fireflies and a large-diameter lower bound. The full statement is settled with both equality characterizations for every n. There is a genuine obstruction to the obvious tools: coefficient monotonicity fails by sign, and majorization fails for every n>=5. No published theorem or source-owned argument implies it. Under the campaign rule, shortness and familiar tools are not an exclusion, and the accepted bunkbed result 382297 passed on a similarly short argument for the same reason.

**Against credit.** Given one classical matrix fact, the lower bound is three lines and the upper bound is one short polynomial identity whose constant term cancels automatically. It is the Wiener-index proof applied one moment higher, with no new idea, no obstacle and no hypothesis to manage; every shift tried works. A specialist would likely call this an exercise once the edge-pair formula is written down. Significance is modest: an extremal conjecture on a chemical-graph-style index. Novelty rests on two search strings.

Why I did not recommend exclusion. The recent exclusions rest on something this case lacks: reuse of the source's own argument (350767, 352895, 344875) or a complete reduction to an actual generic theorem (336276, 362896, 341690, 322479, 328851). Here the source's arguments are unrelated, and no theorem I read implies the target. Excluding would have to rest on the template analogy alone, which the task says is insufficient. If root judges the analogy sufficient, that is a defensible ruling and my mathematics supports either outcome.

Why not PARK. No specific applicable unread proof has been identified, and the failed MATCH item is not one. The remaining gaps are prior-art breadth, which the citing-work check addresses, and the significance judgment itself.

## 5. What would change this

Any of: a paper proving the conjecture or the pair formula with an extremal consequence; a published theorem on Laplacian moments or reciprocal spectra of trees implying it, such as the weak majorization noted above; or a decision that second-moment analogues of the Wiener template are routine per se. Each would move this to EXCLUDE.

## 6. Formal assessment (no Lean run)

The author's Route B identifies the right pieces. Literal endpoint I recommend, in words: for every n>=5, Fintype V with card n, G : SimpleGraph V with G.IsTree,
BH(star_n) <= BH(G) <= BH(path_n), and BH(G)=BH(star_n) iff Nonempty (G iso star_n), and BH(G)=BH(path_n) iff Nonempty (G iso path_n), with BH(G) = n * sum over the non-zero-indexed Laplacian eigenvalues of lambda^{-2}, using Matrix.IsHermitian.eigenvalues of the real Laplacian.

Points the plan should make explicit: remove exactly one zero eigenvalue and prove its multiplicity is one for connected G, so "sum over nonzero eigenvalues" and "i=2..n" agree; include the source's double-sum form as a stated bridge or record that the source prints the two as equal and the endpoint uses the spectral form; define star_n concretely and state isomorphism invariance of BH; include negative controls (BH of P_4 equals 13, of K_{1,3} equals 33/4) as Lean examples.
I agree that the shift is the expensive part. The one-vertex shift has the simplest identity, but tree surgery on arbitrary SimpleGraph data is costly; a finite maximizer argument over trees on Fin n, or a rooted parent-function encoding with a proved bridge, may be cheaper. Dormant only; no dispatch authorized here.

## 7. Process and access record

Network: 4 guarded GET hops of 6 (3 PDF successes, 1 timeout). Searches: 2 of 2 calls, 2 of 6 strings, each precharged and saved in the next tool call. No inherited-denied work requested. Complete TASK.txt (0-12380) and inherited-denials.json (0-309136, 21 contiguous chunks of at most 15000) read before any request.
Own rendered pages actually viewed through Read (5): source pp.1, 9, 10; AIMS p.6058 (pdf p.9); WLY p.20.

Disclosed items. (a) The first runner call after the two mandatory commands failed with exit 126 because run.py is not executable; it never ran and left no receipt; all later calls use python3 -I -B run.py. (b) source_text_section5 repeated the opening of the source because a section search missed; the correct range was then read. (c) get_4_match has true exit 1 (timeout), receipt retained, no retry. (d) pdftotext and pdftoppm wrote work/ files as subprocesses under the runner, not through write_lane; authored text went through write_lane. (e) PROOF.md predates the author read, and the Q1, Q2 and later audit in this file postdates it. (f) Native, transient, writer and supervisor resource peaks are unknown; no universal cap claim.
Protected peers were not accessed. No git, publication, or external message.

## 8. Sources

* Lin, arXiv: https://arxiv.org/abs/2110.09931 (supplied PDF v1)
* Lin, AIMS Mathematics 2022: https://aimspress.com/aimspress-data/math/2022/4/PDF/math-07-04-337.pdf
* Wei, Li, Yang: https://arxiv.org/pdf/2110.02656
* Yi et al.: https://arxiv.org/pdf/1709.02790
