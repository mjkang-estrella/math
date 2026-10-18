# The exact finite coupling debt in T332

Myeongjin Kang, no affiliation. Original prose CC BY 4.0. Author-side continuation, not independent review. All statements below concern sufficient routes to the unchanged full T332 target. None is presented as a substitute theorem or a nomination.

## 1. Coupling and marginal-preserving cut rounding

Fix a finite positively weighted tree T, with all branch vertices included, and probabilities mu_1,...,mu_n on its vertices. Let w_ij=W1(mu_i,mu_j). Let C be the set of vectors

    c_ij(lambda)=E_lambda d(X_i,X_j),  i<j,

as lambda ranges over all joint couplings of these marginals. The coupling polytope is nonempty and compact, and C is compact and convex. Every c_ij>=w_ij.

For K>=1, the following are equivalent:

(A) Some c in C satisfies c_ij<=K w_ij for every pair.

(B) For every collection a_ij>=0, there exists c in C with

    sum_(i<j) a_ij c_ij <= K sum_(i<j) a_ij w_ij.

The forward implication is immediate. Conversely, C+R_+^m is a closed convex set, where m=n(n-1)/2. It is closed because C is compact. If K w is outside this set, strict finite-dimensional separation supplies a nonzero vector a>=0 with

    inf_(c in C) a dot c > K a dot w.

The normal must be nonnegative because the separated set is invariant under addition of every positive coordinate ray. This contradicts (B). Membership of K w in C+R_+^m is exactly (A).

Here (B) is NOT a statement that some deterministic labeling has low cost: it requires a distribution on labelings with EXACT specified marginals. This distinction prevents an arbitrary approximation theorem for metric labeling from being imported without checking its rounding operation.

Root T and set q_i(e)=mu_i(T_e). For a deterministic labeling x_1,...,x_n define S_e={i:x_i in T_e}. Then

    sum_(i<j) a_ij d(x_i,x_j)
      =sum_e length(e) cut_a(S_e),
    cut_a(S)=sum_(i<j) a_ij |1_S(i)-1_S(j)|.

The random sets S_e must obey parent containment and sibling disjointness pointwise, with the root set equal to [n]. Conversely any such family describes a unique vertex label for each i: follow its unique active child until the finite path stops. Exact marginals are equivalent to P(i in S_e)=q_i(e), because vertex probabilities are parent cut masses minus the sum of child cut masses.

For one edge e in isolation, common-threshold rounding S_e={i:q_i(e)>U}, U uniform[0,1], gives

    E cut_a(S_e)=sum_(i<j) a_ij |q_i(e)-q_j(e)|.

It is individually optimal by the elementary bound P(I!=J)>=|E I-E J|. Summing this lower bound over e gives exactly sum a_ij w_ij. The unresolved construction is to achieve a universal multiple of this value while enforcing all the parent/sibling constraints AND the exact marginals simultaneously. Common thresholds enforce parent containment but generally violate sibling disjointness. The exact star obstruction below shows that loss1 is impossible.

## 2. The uniformly chain-weighted first-cost condition is equivalent, not genuinely weaker

For a fixed integer t>=1 consider the following uniform statement, required for every finite marginal family on every finite weighted tree, every reversible A and stationary pi: some joint coupling satisfies

    sum_ij pi_i B_ij c_ij² <= K² sum_ij pi_i B_ij w_ij²,
    B=(1/t) sum_(s=1)^t A^s.                         (C_t)

A universal pointwise coupling with constant K immediately gives (C_t). Conversely (C_t), even at ONE fixed t, implies pointwise coupling with the same K.

First fix a family with pairwise distinct marginals, so all w_ij>0 for i<j. Given arbitrary symmetric weights b_ij>=0, let pi_i=1/n and choose a symmetric generator Q with Q_ij=n b_ij for i!=j and Q_ii=-sum_(j!=i) Q_ij. For sufficiently small epsilon>0,

    A_epsilon=I+epsilon Q

is stochastic and reversible. Since t is fixed,

    (B_epsilon)_ij = epsilon (t+1)Q_ij/2 + O(epsilon²), i!=j.

Choose couplings from (C_t), take a convergent subnet/sequence as epsilon decreases to zero in the finite coupling polytope, divide the inequality by epsilon(t+1)/2, and pass to the limit. Distances and all coupling costs are bounded on this fixed finite tree, so the O(epsilon²) terms vanish after division. Diagonal terms are zero identically. Thus, for every b>=0, there exists c in C with

    sum_(i<j) b_ij c_ij² <= K² sum_(i<j) b_ij w_ij².       (D)

To derive (B) of section1, given a>=0 set b_ij=a_ij/w_ij. The coupling supplied by (D) satisfies, by Cauchy–Schwarz,

    sum a_ij c_ij
      <= (sum a_ij w_ij)^(1/2)
         (sum a_ij c_ij²/w_ij)^(1/2)
      <= K sum a_ij w_ij.

Now use section1. For repeated identical marginals, first apply the statement to distinct representatives and copy the corresponding random variable to every repeated index. This enforces c_ij=0 whenever w_ij=0 and proves the full claim.

Consequences and limits. The B-weighted condition saved in the initial checkpoint is indeed sufficient for the lifted source argument for each instance. But a uniform proof of that condition over ALL reversible chains has the same finite coupling content as the universal pointwise condition. Even discarding finitely many small t does not help: the argument uses any one admissible fixed t and arbitrarily lazy A. This is a statement about this coupling interface, NOT a lower bound for metric Markov cotype or T332. At t=1 cotype itself is immediate by taking nu_i=mu_i, regardless of this stronger coupling problem. A genuinely weaker chain-dependent proof could exploit the source smoothing output, or include extra errors absorbed by the cotype energy; it cannot merely relabel the uniform weighted input-cost bound.

## 3. The unchanged top-down conditional sampler has unbounded tree distortion

This tests the ACTUAL recursive operation in Kleinberg–Tardos §4 when its HST assumption is removed. It does not test all samplers.

Use vertices o,v,a,b,c, edges ov,va,oc of length1 and vb of length L>0. Root at o, so its two components are A={v,a,b} and {c}. Let 0<delta<1/2 and

    mu = delta delta_a + (1/2)delta_b + (1/2-delta)delta_c,
    nu = (1/2)delta_b + (1/2)delta_c.

The exact transport distance is W1(mu,nu)=3delta: couple common mass at b,c and move delta from a to c, and use the tree cut formula for equality.

Consider even the favorable version of top-down conditional sampling: use an OPTIMAL binary coupling for the top component choices and use fresh independent randomness inside A, with the required conditional laws. Because mu(A)=1/2+delta and nu(A)=1/2, the unique optimal binary coupling has probabilities

    P(both A)=1/2,
    P(mu chooses A, nu chooses c)=delta,
    P(both c)=1/2-delta.

Inside A, nu always chooses b and mu chooses b with probability1/(1+2delta), a with probability2delta/(1+2delta). Independence of the lower-level randomness from the top-level choice forces

    E d(X_mu,X_nu)
      = [delta/(1+2delta)](L+2)
        + [delta/(1+2delta)](L+1)
        + [2delta²/(1+2delta)]3
      = delta(2L+3+6delta)/(1+2delta).

The distortion ratio is therefore

    (2L+3+6delta)/(3+6delta),

which is unbounded as L increases. At delta=1/4 it equals(4L+9)/9. The first long-distance term comes from the top-level mismatch; the second comes from conditional renormalization on the event that both enter A. Merely replacing the top-level two-category coupling by an optimal one does not remove the problem.

For any top-level coupling with the prescribed component marginals, P(mu chooses A, nu chooses c)>=delta. Fresh independent conditional sampling inside A therefore already gives expected cost at least delta(L+2)/(1+2delta), regardless of how that top coupling is chosen. Thus the same unbounded-loss conclusion also covers the original top-level rounding rule; the displayed exact ratio is for its favorable optimal-binary variant.

This is NOT an obstruction to universal coupling. The elementary direct coupling displayed above has ratio1 for this two-measure family. Re-rooting or a sampler using local geometry differently could also avoid this example. What fails is the unchanged top-down independent conditional recursion.

The primary proof makes exactly this dependence explicit. Kleinberg–Tardos Lemma4.4 estimates the renormalization error by a root-cut discrepancy times the conditional expected descendant height. Lemma4.3 bounds that height by length(parent edge)/(r−1) under geometric edge decay. Lemma4.1 likewise bounds the separation-event distance by the parent edge scale. Both absorptions are unavailable in this example; they are not technical omissions in the primary statement.

## 4. Universal dominating-ultrametric preprocessing also loses an unbounded factor

This is a separate route diagnostic. Let the label tree be the unit path {0,...,N-1}. Let D be ANY ultrametric dominating ordinary path distance. For s>=0, the relation D(x,y)<=s partitions the vertices into equivalence classes. Each class has ordinary path diameter at most s and therefore cardinality at most floor(s)+1. There are at least N/(floor(s)+1) classes. The sequence of labels0,...,N-1 has at least one transition between successive class-runs for all but the first class represented, so

    #{i in {0,...,N-2}:D(i,i+1)>s}
       >= N/(floor(s)+1)−1.

For 1<=s<=N/4 and N>=4, floor(s)+1<=2s and hence the right side is at least N/(4s). Layer-cake integration gives

    sum_(i=0)^(N-2) D(i,i+1)
       >= (N/4) log(N/4),  N>4.

The same inequality holds after averaging ANY distribution of dominating ultrametrics. Consequently no such preprocessing can have an absolute expected distortion on every adjacent pair. For r-HST metrics in the primary's convention, their leaf distance d_H is within r/(r−1) of the ultrametric that assigns twice the first descending edge scale at the lowest common ancestor. Thus rescaling that ultrametric produces the same logarithmic obstruction up to a constant depending only on r.

Again this does NOT obstruct universal simultaneous coupling on the original path: shared quantiles give distortion1 there. It only shows why importing the ultrametric coupling theorem through a universal dominating-ultrametric representation cannot settle the full tree interface.

## 5. Exact loss1 control

On the three-leaf unit star, let mu_i be uniform on the two leaves other than i. Each pair has W1=1. In any joint coupling the three labels cannot all agree, because their supports have empty common intersection. At least two pair distances are then2, so their sum is at least4 in every outcome. Therefore some pair has expected cost at least4/3. This is the classical three-label obstruction (not claimed new), and is a meaningful negative control for any assertion of simultaneous optimality. It is not an unbounded lower bound.

## Status

No universal finite-tree coupling has been proved or disproved. No chain-specific sufficient replacement has been proved. Sections1–2 identify the exact finite convex/rounding problem and rule out an apparent weakening of it; sections3–5 distinguish failed operations from the still-open full target. The parent has separately supplied an author-side finite-hull ultrapower retraction, whose complete proof was read and checked without a new objection. That removes a separate proposed global obstruction but supplies no finite coupling estimate. The full T332 statement remains unchanged and unresolved.
