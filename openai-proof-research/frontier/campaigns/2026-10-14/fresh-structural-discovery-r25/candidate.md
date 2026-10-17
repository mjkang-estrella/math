# Family 192: cyclic orbit disjointification

Myeongjin Kang, no affiliation. Original prose CC BY 4.0; original code MIT. Third-party materials remain private.

**Pre-freeze complete deduction, not independently reviewed or nominated; counted=false.** The operation below proves a full consequence of the stipulated source. Its contribution may be technical: the new step is a short disjoint-orbit union, followed by equivariance bookkeeping in the source's unchanged mean-cost amplification. No worldwide priority assertion is made.

## Exact consequence proved

For every real C>0, there exist an integer n≥1 and a nonconstant Boolean function f:{−1,1}^n→{−1,1} such that

1. f(x_1,…,x_n)=f(x_2,…,x_n,x_1) for every input;
2. Σ_i f̂({i})>C√deg(f).

Fourier coefficients and real multilinear degree are with respect to the uniform sign cube. No balance or oddness assertion is included. This is the full mathematical statement examined; it is not a scope-frozen campaign nomination.

## Source contract

At pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, the family192 manuscript `Unbounded-Violations-of-the-Square-Root-Degree-Bound-September-26-2026` supplies:

- `02-reporting.tex`, equation `eq:indicator` and Lemma `lem:gaussian`: for all sufficiently large odd m, with q=m+1, the event A has positive Gaussian probability, boundary in finitely many coordinate hyperplanes, and Var(S|A)<1 for S=Σ_{i=0}^{m}G_i. Its indicator is a finite sum of functions using at most q−1 coordinates.
- In that actual proof, R=√(8 log m), h=m^(−3/2), a_j=1−R+2R(j−1)/(m−1), I_j=[a_j−h,a_j+h]. The event requires all leaves except the selector's chosen leaf to belong to their prescribed I_j, and the chosen leaf to fail its test. Thus each point of A has q−2 constrained coordinates.
- `04-mean-cost.tex`, Lemma `lem:refinement`, Lemma `lem:mc-transfer`, and Theorem `thm:mean-cost`: a finite Gaussian partition with cell coordinate costs ℓ, Gaussian-null boundaries, and retained score variance V greater than mean cost c can be iterated on finite sign cubes. Typical cost-word truncation gives observations F with unbounded v(F)/D while E|T_F|>√v(F)/2, where T_F=E[H_n|F] and every cell indicator has degree ≤D. Its sign readout has degree ≤D and signed linear sum E|T_F|.

The source is accepted as true; the symmetry steps below are proved independently. All nine source files, including all alternative/weighted/small-width companions, were read. None states this cyclic conclusion. Exact raw-source identities are in source-receipt.json.

## 1. Disjoint cyclic copies of the rare event

Choose a sufficiently large odd m≥5 satisfying the source Gaussian estimates and also h<R/(m−1). The latter holds eventually, since (m−1)m^(−3/2)/√(8 log m) tends to zero. Consequently all the closed intervals I_1,…,I_m are pairwise disjoint. Put coordinates on Z/qZ, with central role 0 and leaf roles 1,…,q−1, and let τ shift these roles cyclically.

We claim τ^a A and τ^b A are disjoint whenever a≠b mod q. Suppose a point belonged to both. The first membership constrains all coordinates except its central position and its selected leaf; the second also leaves at most two positions unconstrained. Therefore at least q−4≥1 positions are constrained by both. At any such position, the two assigned leaf roles differ by a−b mod q and hence are distinct nonzero residues. The coordinate would belong to two disjoint leaf intervals, a contradiction. This argument covers every real input and all endpoint conventions.

Let E be the union of the q translates. It is cyclic invariant and

1_E=Σ_{a=0}^{q−1}1_{τ^a A}

pointwise. Each summand retains the source coordinate-order bound q−1; therefore so does E. Its boundary is contained in the union of the translated finite hyperplane sets. For the iid Gaussian vector, both its law and S are permutation invariant. Disjointness consequently gives, for every bounded measurable φ,

E[φ(S)1_E]=q E[φ(S)1_A],  P(E)=qP(A)>0.

Thus the conditional distribution of S given E equals that given A. In particular Var(S|E)<1. This is an exact identity; we do not average conditional variances of different laws.

## 2. Equivariant complement refinement

Apply the source refinement lemma to E, using the same finite one-dimensional grid in every coordinate. The partition has one special label for E, of cost q−1; its other labels specify E^c intersected with an ordered grid box, of cost q. Empty labels are harmless. Cyclic permutations act on these labels by rotating the grid indices and fixing the special label. The partition map P is equivariant and the cost ℓ is invariant. The source error estimate, with a sufficiently fine common grid and sufficiently large finite cutoff, gives V>c. No asymmetrical grid is needed by that estimate.

## 3. Equivariance through the full amplification

We give the extra induction absent from the source statement. For an observation F on a uniform n-bit cube, suppose its score T_F is invariant under a permutation group G containing an n-cycle. The source also maintains its finite cell-degree bound D, v(F)>0, and the normal-approximation invariant from the proof of `thm:mean-cost`.

Initially F=H_N is the sum of N independent signs, so its score is invariant under every permutation, in particular an N-cycle. Choose N sufficiently large exactly as in the source.

Apply P to the standardized scores of q independent copies of F. Every element of G acting separately inside the q blocks fixes these scores. The cyclic group C_q on the blocks permutes the partition label by its label action. Thus the new group label L is equivariant under H=G wr C_q; its degree cost is unchanged by H. The notation denotes the usual imprimitive action on q blocks of n positions.

Now take K independent copies of L. Keep each label word whose total cost is at most K(c+δ), and merge the other words into one failure label, precisely as in the source. The resulting observation F'_K is equivariant under H^K and cyclic permutation C_K of the K batches: all these actions preserve total cost, permute retained labels, and fix failure. Hence it is equivariant under H wr C_K.

For completeness, equivariance implies score invariance on the finite cube. Each input permutation preserves uniform measure and H_{nqK}; it bijects the fiber of any attained label onto the fiber of its transformed label. Their conditional averages of H_{nqK} agree. Consequently T_{F'_K} is invariant under H wr C_K. Unattained labels need no conditional expectation and cannot affect any input assertion.

The source's degree bound DK(c+δ), fourth-moment failure estimate, convergence in distribution, and strict ratio increase remain exactly the same. Symmetry imposes no restriction on how large N or K must be. Therefore the entire finite iteration preserves this additional score invariance, while obtaining arbitrarily large v(F)/D with E|T_F|>√v(F)/2.

## 4. A full cycle and Boolean readout

If G contains an n-cycle γ, then G wr C_r contains an nr-cycle. Label positions (b,a) with b in Z/rZ and a in Z/nZ along γ. The permutation sending (b,a) to (b+1,a) for b<r−1 and (r−1,a) to (0,a+1) belongs to the wreath product and is a single nr-cycle. This applies twice at every induction step. Thus the final score is invariant under one cycle visiting every input coordinate.

Choose sufficiently many amplification steps that v(F)/D>4C². The sign readout f=sign(T_F), with the same fixed sign at zero as the source, inherits every score symmetry. It satisfies

Σ_i f̂({i})=E[f H_n]=E[f T_F]=E|T_F|>C√D≥C√deg(f).

The positive signed correlation excludes constants. Relabel the coordinates in the order of the full cycle. Relabeling preserves the signed linear sum and degree, and makes f invariant under the standard cyclic shift. This proves the consequence with its full every-C quantifier.

## 5. What the failed seed searches do and do not say

The earlier idea sought one balanced cyclic seed with linear sum greater than √degree, then ordinary self-composition. The twelve recorded MILPs did not find one. They range over selected n=6,…,12 and degree bounds3,…,6; n=12,d=6 timed out. Solver infeasibility and numerical optima are not accepted as rigorous universal certificates. Every returned table was checked by exact integer Walsh transform for its degree, balance when requested, and cyclic invariance. The record is exploratory only and is not used in the proof above.

There is a separate exact obstruction to balanced cyclic seeds at odd prime powers. If n=p^a for odd prime p, every nonconstant binary word has cyclic orbit size divisible by p. Write u=f(1,…,1), v=f(−1,…,−1). Balance implies u+v≡0 mod p. Since u,v∈{−1,1}, this forces u=−v. If degree<n, the unnormalized full Walsh coefficient is zero. Modulo p its orbit sum is u−v (n is odd), forcing u=v, contradiction. Thus every balanced cyclic Boolean function at such n has degree n. The proof above imposes no balance and is unaffected.

## Contribution boundary

The actual unpaid step found was preserving Boolean/event-valuedness during symmetrization without increasing coordinate degree or conditional variance. Disjoint role intervals solve it for the source's particular event. All probability amplification and degree saving remain source operations; conditional-expectation equivariance and the wreath-product carry cycle are elementary. This may be a useful exact corollary but does not by itself meet the campaign's substantial-contribution gate, which explicitly excludes mere finite-union bookkeeping and routine transfer. No self-awarded proof PASS, contribution PASS, acceptance, count, or publication step is claimed.
