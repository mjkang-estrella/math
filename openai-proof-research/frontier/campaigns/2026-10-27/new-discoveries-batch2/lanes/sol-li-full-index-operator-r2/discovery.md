# Full Li target unresolved; credit 0

Exact target: Jiangtao Li, arXiv:2609.03653v1, Conjecture 1.6. For EVERY pair of nonempty finite positive integer indices k≻l (proper extension is larger; otherwise smaller first unequal component is larger), H_l=H_k∘p on the unit disk with holomorphic p:D→D, p(0)=0, all Taylor coefficients strictly positive and total sum ≤1. H_k=Li*_k/z, with removable value 1 at zero. No change of normalization, order, or admissible indices is made.

The source definition, conjecture, moment-density recursion, shifted univalence proof and Section 4 quotient, strict-MLR, logarithmic-derivative and boundary-separation proofs were read. Current arXiv abstract bytes at 2026-10-29T09:22:49Z match the r22 observation and show v1 only. The exact saved TeX/source archive hashes are retained. No journal counterpart is asserted. The whole r22 mathematical handoff and root uniform-operator notes/checker were reconciled. Campaign counts remain 5/30 additional, 35/60 total, and Fenner remains excluded by Jin's October 14 same-object proof.

## Uniform first-index operator independently checked

Write H=1+Σ a_n z^n and T H(z)=∫_0^1 H(tz)dt. The literal source finite sums give H_(k1+1,tail)=T H_(k1,tail). Comparing coefficients in H(p)=T H gives

c1=1/2,
c2=a2/(12a1),
c3=a3/(8a1)−a2²/(12a1²),
c4=11a4/(80a1)−3a2a3/(16a1²)+11a2³/(144a1³).

These agree with the root formulas by an independently implemented exact composition algorithm. Positive Hausdorff moments with a1>0 give a2²≤a1a3, hence c3≥a3/(24a1)>0. With m1=a2/a1, m2=a3/a1, m3=a4/a1, log-convexity gives m2≥m1² and m3≥m2²/m1. Thus c4 is at least m1³(11r²/80−3r/16+11/144), r=m2/m1²≥1. Its derivative is positive for r≥1 and its value at 1 is 19/720. This proves only four coefficients, an elementary uncredited helper.

No valid induction from these inequalities to all coefficients was found. The exact recurrence subtracts positive terms:

c_n=(b_n−Σ_{j=2}^n a_j [z^n]p^j)/a1.

Hausdorff log-convexity does not supply an established all-order bound on that subtraction. The r22 exact strict-MLR atomic counterexample remains a method obstruction, not a Li counterexample and not a counterexample to this particular T relation.

Independent diagnostics: explore.py uses 90-decimal mpmath arithmetic, seed 261029, degree45: 100 atomic laws and 200 genuine ordered Li pairs, no coefficient below −10^-65. Pairs include first-index increments, proper extensions by16, and different tails. These are numerical diagnostics, not exact certificates or positivity proofs. Its 72 extra tests concern the dilation generator (H_k−1)/H'_k; for nonsingleton k this is NOT the proper-extension limit below. That distinction is explicit in the script.

## A source-specific proper-extension falsifier criterion

For k=(k1,...,kr) define the convergent power series with zero constant term

B_k(z)=Σ_{m≥2} z^(m−1)/m^k1 · Σ_{m≥m2≥...≥mr≥2} (m2^-k2 ... mr^-kr).

For r=1 the inner sum is 1, so B_(a)=H_(a)−1. For longer indices it is different. For each FIXED n, direct expansion of the last harmonic sum gives

2^q(A_(k,q)(n)−A_k(n)) → [z^n]B_k.

Indeed the appended innermost variable j=2 contributes exactly B_k; the remaining j≥3 terms are nonnegative and are bounded by (2/3)^q (n+1) A_k(n). This follows by bounding their number by n+1 and dropping the lower restrictions in the outer sum. The bound is coefficientwise, with no uniform assertion as n→∞.

Let p_q be the unique LOCAL analytic germ satisfying H_(k,q)(p_q(z))=H_k(z). Its existence follows from A_(k,q)(1)>0. Formal inversion at the identity, or differentiation of the finite triangular coefficient equations, now gives, coefficient by coefficient,

2^q(p_q(z)−z) → −B_k(z)/H'_k(z).

To justify this without a global inverse: for every fixed degree N, the inverse-composition coefficients are rational functions of finitely many source coefficients with nonzero linear denominator. Taylor expansion of these finite functions at H_k proves the displayed first variation. The identity variation is H'_k·δp+B_k=0. The perturbation is O(2^-q), so the quadratic remainder vanishes after scaling by2^q.

Consequently a positive coefficient [z^n](B_k/H'_k)>0 for some actual finite k and n≥2 would produce a genuine negative inverse coefficient for sufficiently large finite q. This would refute Conjecture1.6, regardless of whether its global-subordination part holds. A concrete finite q would still require exact certification. No such positive coefficient was found.

check.py verifies 24 actual indices through degree18 in exact Fraction arithmetic: the finite-q error bound at q12, every coefficient of the quotient recurrence, and 48 genuine inverse-composition identities (all positive). tail_probe.py separately tests 450 actual indices, depths1..12/components1..12, through degree40 at100 decimals, no positive generator coefficient above10^-80. This is a directional test, not a proof of the necessary all-order inequality. It is not an eligible helper nomination.

The source additionally proves P_k=z(H_k−1)'/(H_k−1) belongs to the Hausdorff–Stieltjes class. Thus the dilation generator is z/P_k. Classical reciprocal-moment/Kaluza sign machinery is a plausible explanation for its observed signs, but does not identify B_k/H'_k for general tails. No unproved promotion from one generator to the other is made.

## Primary theorem comparison and bounded registry screen

The r22 complete scoped trees are saved here, SHA256 checked against its provenance: Omega D5 12478 and Problems1541, OpenAI preprints13578, Count183 and AIM3541 entries, all truncated=false. registry-screen.json contains their heads, tree SHAs, full path scan and inherited observation boundary. These are complete scoped Git trees, not a1000-entry listing. The GitHub API rate-limit403 at09:06UTC was respected: no retry, credential switch, raw-head substitution or claim that these heads were independently re-observed. Current public web queries for Li/polylogarithm and named registries were supplementary and yielded no usable exact target result. Search-engine omission is not freshness or novelty clearance.

Nearest actual registry bodies located in the Omega tree were available in an earlier complete checkout. CompositionDisk.lean and CompositionRecurrences.lean were read; their exact saved bytes match the current inherited tree's Git blob SHA1 (not merely filenames). They define STRICT nested sums associated with Xu–Zhao, factor out their depth zero, and prove single-function positive coefficients/geometry and differential recurrences. They do not assert the weak-star Li pairwise compositional inverse statement. See nearest-registry-bodies.json for immutable URLs/hashes. No Lean replay was run. Further modules in that family were not exhaustively audited, so no family-wide absence claim is made.

Current clopen homepage retrieved at09:22:50UTC is byte-identical to the r22 homepage. This supplies a current homepage observation only, not exhaustive registry coverage. The targeted clopen query in r22 and search queries do not certify absence.

Actual classical primary bodies read: Bakan–Ruscheweyh–Salinas, arXiv:1804.03931v1, definitions and Theorems2.1–2.3,2.8 and the latter proof, concerning Pick/logarithmic derivative classes and universally starlike representations. These are single-function characterization results; no same-object inverse-coefficient resolution was located in the portions read. Their 2015 AMS polylogarithm primary PDF returned403 via web fetch; stopped, body gap retained. Lewis1983 and original Bernardi1969 bodies remain unread; no novelty clearance from abstracts or secondary summaries.

Stacey Muir's author-hosted 2007 paper was fetched and actual Theorems2,4,6,7 and proof of2 read. Theorem2 assumes every member F_lambda of its differential equation is convex; Theorem7 gives a Bernardi chain under convexity of the input. Neither theorem states positivity of all coefficients of the intervening Schwarz map. This is relevant subordination machinery, with hypotheses that must be proved for any proposed source instance. The paper's source normalization and scalar factors also matter. It is not used to claim the full Li result. Kamano's actual preprint remains the r22 real-order comparison; published body403HOLD remains unchanged.

The strongest eligibility objection is that subordination alone may follow routinely from Li's own univalence and boundary separation, or from classical integral-mean theory. Such a result alone would earn0. Actual all-order strict coefficient positivity for every ordered pair has not been proved. No absence-certified or worldwide novelty claim is made.

## Remaining gap and reproducibility

No full proof, genuine negative Li coefficient, global analytic continuation of p, disk-image inclusion, or sum bound is established. If all coefficients were nonnegative AND p were a disk self-map, the sum bound would follow routinely by monotone convergence along r↑1; neither premise is silently assumed.

Run check.py with the launch limits in run-checks.sh. It uses only the Python standard library; explore.py and tail_probe.py additionally require mpmath. Every mathematical script has hard512MiB address space, CPU and alarm limits, also set at launch; BLAS1 and fixed seed. No Lean, PROOF.md, nomination, external mutations, git, children or shared writes. Final status UNRESOLVED, discovery_count_credit=0.
