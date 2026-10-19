# Countable contractions: a renewal calculation before any freeze

This is a compatibility calculation, not a candidate. Actual analyticr26 `countable-feasibility.md` already develops finite-entropy type truncation, the b! conditional order bound, first-moment contraction truncation and tight overshoots for increments bounded below by a positive constant. Actual analyticr113 `operation-comparison.md` also credits these operations. The latter was found/read later in this round, still before any freeze.

The source148 `windows.tex` is stronger than a fixed-scale estimate: its conditional fair-pair gain averages the unobserved future before convexity, and its disjoint-window argument allows arbitrary finite band endpoints B_n. `corollaries.tex` applies the exact entropy-rate formula. These operations were read; the entire source proof was not reread.

Here is the elementary renewal extension checked in this round. Let Y_j>0 be iid, with E Y_1<infinity, set S_0=0 and S_n=sum_(j=1)^n Y_j, and tau_x=min{n:S_n>=x}, x>0. Choose a>0 with p=P(Y_1>=a)>0. For every half-open interval J of length a,

    E number{j>=0:S_j in J} <= 1/p.                            (1)

To prove (1), stop at the first renewal position at least the left endpoint of J (or start at zero if that endpoint is negative). If the position is outside J the count is zero. Otherwise, after each counted position a fresh increment at least a exits J permanently. The number of possible counted positions is dominated by a geometric waiting time of mean 1/p. Independence at this genuine stopping index justifies the bound. Positivity and p>0 also imply S_n tends to infinity almost surely.

If S_(tau_x)-x>M, some j has S_j<x and Y_(j+1)>M+x-S_j. Partition the nonnegative deficits x-S_j into intervals of length a. Independence of Y_(j+1) from S_j, a union bound and (1) imply

    sup_(x>0) P(S_(tau_x)-x>M)
      <= (1/p) sum_(l>=0) P(Y_1>M+l a)
      <= (1/p)[P(Y_1>M)+(1/a) integral_M^infinity P(Y_1>t) dt]. (2)

Use deficit bins [la,(l+1)a), corresponding to renewal-position intervals (x-(l+1)a,x-la]; the same geometric exit argument proves (1) for this half-open convention. This gives the displayed strict-tail bound including atomic increments. The right side tends to zero. Thus finite mean gives uniform tightness of these overshoots without a deterministic positive lower bound on each increment. This standard renewal mechanism supplies the particular random-clock truncation, not an entire new dimension theorem.

For contractions, Y=-log|r|, (2) makes the scale distortion at a stopping time bounded outside an event of small probability. That fits the existing stopped-mixture window comparison in r26. It does not by itself handle a countable family with arbitrary translations, replace projection entropy by random-walk entropy, prove exact dimensionality in a new noncompact setting or supply all source uniformity assumptions.

The closest retained primary is arXiv:1405.2942v2, whose definitions use a common compact set, uniform contraction and conformal extensions; Corollary3.14 uses projection entropy. The actual defining assumptions and the indicated theorem/corollary proof passages were inspected with the partial extents in reading-limits.md. It is not cited as a theorem with arbitrary noncompact translations or as an identification of projection entropy with the source's group-walk entropy. No full broadened theorem was frozen or proved. This renewal lemma is not promoted as a replacement, and no claim of newness is made.
