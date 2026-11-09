# MathDB 341439: ordinary proof investigation

Outcome: HOLD, credit 0. No all-n proof or counterexample to the actual signed polynomial was obtained. The useful new deductions are an exact failure of the proposed pathwise sufficient inequality, a valid local synchronization lemma with a demonstrated limit, and a source-derived two-step coefficient recurrence. These are helpers, not eligible discoveries. Campaign remains 52/60. No Lean endpoint is proposed for execution.

## Literal object and source bridge

The actual source is Lin–Wang–Zeng, arXiv:1812.09098. Write

    E_k(t,q) = sum_{pi in S_k} t^exc(pi) q^(maj(pi)-exc(pi)),
    T_n(t,q) = 1 + t sum_{k=1}^n [n choose k]_q E_k(t,q).

Gaussian coefficients here are polynomials evaluated at -1, not undefined quotients at -1. The equivalent signed enumerator in Theorem 1.1 is

    T_n(t,-1) = sum_{pi in PRW_(n+1)} (-1)^ai(pi) t^des(pi).

PRW consists of permutations whose first ascent is at the letter 1, if there is an ascent. An admissible inversion (pi_i,pi_j), i<j, is an inversion with either i>1 and pi_(i-1)<pi_i, or an intermediate k with pi_i<pi_k. This is not the inversion-sign descent enumerator on all permutations.

For k>=1 let E_k(t)=sum_{pi in S_k}t^des(pi). In Corollary 2.3 only, E_0=0. Define B_0=1 and

    B_m = 1 + t sum_{k=1}^m binom(m,k)(1+t)^k E_k(t),
    O_m = 1 + t sum_{k=0}^m binom(m,k)(1+t)^k (E_k(t)+E_(k+1)(t)).

Corollary 2.3 gives T_(2m)(t,-1)=B_m for m>=1, and T_(2m+1)(t,-1)=O_m for m>=0. In particular O_0=1+t. Source (4.1) calls B_m=A*_m. Source Corollary 2.4 gives a positive convolution for O_m, but a difference of convolutions for the next B row; the subtraction cannot be dropped.

The target is, for every n>=1 and every 1<=j<n,

    ([t^j]T_n(t,-1))^2 >= [t^(j-1)]T_n(t,-1) [t^(j+1)]T_n(t,-1).

Extending coefficients by zero to every integer adds only trivial exterior inequalities. The J-fraction expansion gives B_m strictly positive coefficients throughout [0,2m]: its all-level path already contributes b_0^m with positive coefficients throughout this interval. Equation (2.6) gives O_m positive throughout [0,2m+1]. Their endpoint coefficients are 1 and their degrees are exactly 2m and 2m+1. All further arguments use these conventions.

V1 Conjecture 7.2 and v2/v3 Conjecture 5.2 have the same all-n signed target. Latest Theorem 1.3 proves symmetry and unimodality only. The current arXiv abstract was freshly retrieved unchanged (same SHA256 as r298), listing v1 2018-12-21, v2 2019-02-05, v3 2020-05-15. Relevant bodies and identities, not every page of all three versions, were compared. The journal is European J. Combin. 78 (2019), 105–120, DOI 10.1016/j.ejc.2019.01.010. Its previously denied final route was not retried. No separately authenticated final journal body or correction was obtained; journal/corrections/citing-literature clearance remains incomplete.

## Route 1: actual paths defeat universal pairwise synchronization

Source (4.6)–(4.8) is the ordinary Motzkin moment expansion with up-step weight 1, level weight

    b_h=(h+1)+(2h+1)t+(h+1)t^2,

and down-step from height h weight lambda_h=h^2 t(1+t)^2. A path of length m from 0 to 0 has d up steps, d down steps, and m-2d levels. Its weight has interval support [d,2m-d] and symmetry center m. Each factor is log-concave and so is each product, by convolution. These facts do not control the sum.

There is an exact obstruction within this actual path family, not just a generic example. For length four take P=HHHH and Q=UUDD. Then

    f=b_0^4=(1+t+t^2)^4,
    g=lambda_1 lambda_2=4t^2(1+t)^4.

At j=1, f_0=1, g_0=g_1=0, g_2=4. Thus

    M_1(f,g):=2 f_1 g_1-f_0 g_2-g_0 f_2 = -4.

This refutes the suggested universal pairwise mixed-minor criterion on actual terms. It does NOT refute log-concavity of B_4 or any T_n. Indeed even the minor of f+g at j=1 is 4^2-(10+4)=2, because f's own minor supplies slack. This is hand algebra on two specified paths, not an enumerative search.

More generally, whenever two actual path terms have down counts d and e>=d+2, at j=e-1 the narrower term vanishes but its next coefficient and the wider term's previous coefficient are positive. Their M_j is negative. Consequently neither strong synchronization nor weak synchronization nor partial synchronization can hold pairwise for the entire path family. Positive rescaling and reordering cannot fix this.

Grouping by down count alone also does not fix the proposed sequential criterion. If C is the sum of terms with down count below d and W_d the sum with down count exactly d, then C has positive constant coefficient while W_d starts at d. For d>=2, M_(d-1)(C,W_d)=-C_(d-2)(W_d)_d<0. Thus a proof that merely adds these blocks while asserting weak synchronization is impossible.

What remains possible is compensation by self-minors or by other pairs. Precisely, for any partition of the actual path set into blocks F_i,

    Delta_j(sum_i F_i)=sum_i Delta_j(F_i)+sum_(i<l) M_j(F_i,F_l).

The next lemma must establish nonnegativity of this entire right side, or charge its negative terms injectively to positive ones with exact multiplicities. Nonnegative mixed minors alone are unnecessarily strong, and the straightforward all-pairs version is false.

## Route 2: a valid local convolution move, and why it does not finish

Primary criterion checked: Gross–Mansour–Tucker–Wang, *Log-Concavity of Combinations of Sequences and Applications to Genus Distributions*, retained author PDF, Section 2.1. Strong synchronization means both sequences are nonnegative log-concave, with a_j b_j >= a_(j-1)b_(j+1) and >= a_(j+1)b_(j-1) for every integer j. Theorem 2.2 gives positive-sum log-concavity; Theorem 2.8 preserves strong synchronization under convolution with the SAME nonnegative log-concave sequence without internal zeros. The hypotheses include the mixed inequalities; they are not consequences of equal centers.

There is one legitimate local application here. At any fixed height h, the length-two alternatives HH and UD have weights b_h^2 and lambda_(h+1). Up to positive constants their coefficients are

    F=(1,2r,r^2+2,2r,1), G=(0,1,2,1,0),
    r=(2h+1)/(h+1), 1<=r<2.

Both are log-concave with interval support. At j=1 and 3 the nontrivial strong inequality is 2r>=2; at j=2 it is 2(r^2+2)>=2r; at exterior indices both sides needing comparison vanish. Hence these alternatives are strongly synchronized for every h>=0. Their products with a common path context remain synchronized by Theorem 2.8. One can legitimately pair these two local configurations, retaining their actual height factors.

This only treats a local move, not arbitrary paths or packets. Synchronization is not transitive. Moreover long arches already defeat a tempting stronger extension: at height zero compare H^(ell+2) with U H^ell D, ell>=1. Their weights are b_0^(ell+2) and lambda_1 b_1^ell. The strong inequality at j=1 would require

    ell+2 >= 2+(3/2)ell,

after cancellation of the common positive scalar 2^ell, and is false. This does not assert failure of the weaker criterion for this particular pair.

The distinction between strong and weak convolution is essential. Hu–Wang–Zhao–Zhao, arXiv:1507.08430, Definition 2.2 and Example 2.3 disprove general preservation of WEAK synchronization under convolution. Their Definition 3.2 requires partial synchronization for every pair of indices p>=q:

    a_p b_q+a_q b_p >= a_(p+1)b_(q-1)+a_(q-1)b_(p+1).

Theorem 3.7 preserves that stronger condition under a common log-concave convolution. The actual full path family fails even its p=q instances above. Their proof uses diagonal telescoping and log-concavity, not an unrestricted weak-convolution theorem. No source theorem here supplies the missing actual packet partition.

Concrete next lemma: construct disjoint packets of the colored weighted paths, with local HH/UD alternatives and height-correct contexts, whose packet polynomials have a proved partial-synchronization relation (including all exterior coefficients). A connected graph of valid local moves is insufficient. No such packet construction was found.

## Route 3: exact two-step recurrence, including the odd bridge

This route reduces the negative quadratic sum to a single previous-row correction. Source Lemma 4.3 gives

    F(x,t)=sum_m B_m(t)x^m/m!
          =(1-t)e^x/(1-t exp((1-t^2)x)).

All calculations below are formal; the geometric expansion is t-adic and no analytic convergence assumption is needed. Put c=1-t^2, S_m=B_m/(1-t), and

    S_m=sum_(r>=0) t^r(1+rc)^m,
    R_m=sum_(r>=0) r t^r(1+rc)^m.

Then S_(m+1)=S_m+c R_m and t S'_m=R_m-2m t^2 R_(m-1). Eliminate R_m and R_(m-1), and multiply by 1-t. For m>=1 this gives the exact polynomial identity

    B_(m+1)=[1+t+(2m+1)t^2]B_m
             +t(1-t^2)B'_m-2m t^2 B_(m-1).                 (R)

B_0=1, B_1=1+t+t^2. Thus, writing b_(m,j)=[t^j]B_m and setting exterior indices to zero,

    b_(m+1,j)=(j+1)b_(m,j)+b_(m,j-1)
             +(2m+3-j)b_(m,j-2)-2m b_(m-1,j-2).           (C)

The last term remains a subtraction. Neither ordinary row log-concavity nor positivity alone makes (C) an LC-preserving operator. A useful simultaneous induction would bound the previous-row term against the exact slack of the first three terms. It must also cover reflected high indices: (2m+3-j) is not nonnegative for unrestricted j, even though the zero conventions make (C) valid everywhere.

There is also an exact compact odd identity

    (1+t)O_m=B_(m+1)+t B_m, for every m>=0.              (O)

Proof: let U(z)=sum_(k>=0) E_k^std(t)z^k/k!, where E_0^std=1, in contrast to the source summation convention E_0=0. The binomial-transform definitions give F=(1-t)e^x+t e^x U((1+t)x), and the odd EGF H=(1-t)e^x+t e^x[U((1+t)x)+U'((1+t)x)]. Differentiating in x gives F_x=F+t(1+t)e^x U'((1+t)x), whence H=(F_x+tF)/(1+t), proving (O).

Even a proof that all B_m are LC would not automatically prove all O_m are LC: division by 1+t does not preserve LC. Exact coefficients can instead be tracked by

    o_(m,j)+o_(m,j-1)=b_(m+1,j)+b_(m,j-1), o_(m,-1)=0,

or the finite alternating expression obtained by iterating this equation. A simultaneous proof of minors for b and o is necessary unless a separate valid division lemma is established with verified hypotheses. This is a semantic bridge, not a recurrence-only replacement for the signed target.

Concrete next lemma: for arrays b,o defined by the source polynomials and (C),(O), establish a closed simultaneous collection of inequalities which absorbs -2m b_(m-1,j-2) and implies BOTH adjacent minors. Row LC alone has not been shown invariant; no stronger invariant is claimed proved. Generic real-rootedness is unavailable already for B_1=1+t+t^2.

## All-n boundary minors are settled, but remain helpers

Using [t]E_k=2^k-k-1 for k>=1 and E_k(0)=1 gives, for all m>=0,

    b_(m,0)=1, b_(m,1)=2^m-1, b_(m,2)=3^m-2^m.

For the middle formula at k=1, the Eulerian t coefficient is zero as required. These formulas also give the correct zero exterior values when m=0. Thus

    Delta_1(B_m)=4^m-3^m-2^m+1 >=0.

For m>=1 expand 4^m-3^m as sum_(i=0)^(m-1)4^(m-1-i)3^i. Termwise this dominates the analogous sum for 2^m-1, since 4>=2 and 3>=1. The case m=0 is equality. Symmetry gives the reflected boundary minor. The endpoint minors themselves are 1 under zero extension.

The odd definition similarly gives

    o_(m,0)=1, o_(m,1)=2^(m+1)-1,
    o_(m,2)=3^(m+1)-3*2^m.

Indeed the t coefficient of (1+t)^k(E_k+E_(k+1)) is 3(2^k-1), also at k=0 using E_0=0. Therefore

    Delta_1(O_m)=4^(m+1)-3^(m+1)-2^m+1 >=0,

by the preceding difference-of-powers bound, which is stronger than needed. Symmetry covers the other end, and m=0 has no internal minor to check. This leaves the genuine interior indices, not a boundary/domain defect.

## Source, history, registry and qualification gates

The complete r298 ATTEMPTS.md was read, including its rejected generic common-center inference, unavailable real-rootedness route, other source-family exclusions and correction precedent. Its keyed result/provenance, exact raw 341439 record, source inventory, registry review, history matches and denial receipt were inspected. The historical hit for 341439 is a reservation in the shared ledger, not an accepted solution. No accepted signed-Eulerian family was found in the bounded accepted-entry review; this is not an exhaustive historical proof-body search. Current STATUS and ledger agree on 52/60. Inherited accepted source families and zero-credit known-result/routine-bridge/correction precedents remain in force.

Public GitHub head pages were freshly read: OpenAI 4eaee87548250b2682affda7d05d947c05554bae and LeanPool 01db1d7049cf9668bda1e9e106875ee1278b43e6 agree with r298, so its immutable-at-head CONTENTS / root import / projects index screen is reused. Omega advanced from r298 deffee7663cc3d0c6b93a2db739b699b48d9b643 to 327c2bbac60acd78f1290ab427f085d0cdd8943b; the new pinned README and commit page were fetched. Commit timestamp is 2026-11-06T11:23:30+08:00. The README has no exact ID/source/family string hit. None of these indexes provides exhaustive statement-level novelty clearance, and absence is not a proof of priority. See receipt JSONs for URLs, times and hashes. No API or denied-route workaround was used.

A fresh lawful primary journal copy of Cui–Liu–Yuan, *Generalized Eulerian distributions from the wreath product C_r wr S_n*, Indian J. Pure Appl. Math. 56 (2025), 125–139, online 2023-07-15, was retrieved from the Indian National Science Academy. Section 3.4 identifies exactly B_m, equation (23), and its Proposition 33 establishes strong q-log-CONVEXITY in the row index, not coefficient log-concavity within B_m. Thus it neither resolves the target nor supplies a complete routine bridge. This body is a useful negative applicability check; only its relevant section, introduction and criteria were read. Bounded searches located no full signed-LC resolution or correction; inaccessible/unindexed literature remains unknown.

No published full theorem or complete routine classical reduction was demonstrated here, so no such exclusion is asserted merely on grounds of ease. The actual outcome is unresolved mathematics plus incomplete final-journal and prior-art qualification. If a complete existing bridge is later found it must receive zero credit with that bridge written explicitly. These helpers do not satisfy the exact endpoint, independent review, paper or Lean requirements.

No dormant Lean build or numerical diagnostic is recommended: the strongest proposed universal helper is already disproved exactly, and no bounded calculation here would decide the all-n aggregate or recurrence invariant. A future fully qualified proof would still have to formalize the actual signed PRW enumerator (or the Gaussian/Eulerian definition with proved equivalence), Corollary 2.3, both parity branches, zero conventions, and all n/j coefficient inequalities. A recurrence proxy alone would not qualify.

All writes stayed in this assigned lane. No children, Lean, solvers, numerical/enumeration search, git operations, author/shared edits, publication/contact/browser/account actions or Crown/r299 work occurred. Source downloads and administrative hash/text processing are the only local execution. Initial short bootstrap reads lacked explicit per-process caps/log wrappers; this is disclosed, not retrospectively claimed compliant. Subsequent substantial download jobs had CPU 120 s, wall 140 s and AS 6 GiB bounds with at most two CPUs via affinity; all returned and were reaped. Web managed-search resource caps are unknown. See JOBS.md and frozen-before/after.json for receipts and preservation.
