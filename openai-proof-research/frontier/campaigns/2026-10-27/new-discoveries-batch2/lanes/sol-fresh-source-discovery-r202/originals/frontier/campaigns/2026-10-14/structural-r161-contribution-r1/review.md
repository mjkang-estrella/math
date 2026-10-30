# Conditional contribution review of T126S161

**Verdict: TECHNICAL, conditional on correctness, for the entire unchanged frozen statement.** This is a contribution assessment only. No correctness verdict, acceptance decision, campaign count, or worldwide-priority claim is made. The parent alone integrates. The author assigned no contribution grade, and none was assumed.

The target is exactly the three-conclusion statement in [the authenticated frozen input](private/frozen/scope-frozen.md), SHA256 `b5c7b51d352e250df511fae5d3456ccbaa2756180111020b3108415c12a7d813`. In particular this assessment includes every q>=3 and ell>=1, every allowed N and positive cell-size vector, every admissible table including zero entries and arbitrarily rare/unbalanced cases, the stated all-N qth moment, the exact stated d and N0 for every real K>0, and the single simultaneous degree-d polynomial for every d>=0, fixed Z and arbitrary real f. It does not substitute a balanced, dense, asymptotic-only, symmetric-f, or special-table theorem.

The decisive reason is a complete compatible classical reduction. The literal finite type-class bounds give the stronger estimate

    tr((T_t^* T_t)^q) <= (N+1)^E,
    E = ell^q + q*ell + q*(m(q,ell^2)+ell^2+2*m(q,ell))
      = C(q,ell)-1-3q.

Below is the derivation, including every conditioning normalization. Its only entropy step is the standard tree-projection identity plus coordinate data processing. It therefore pays the operation offered in author-proof Sections 2-4 without requiring a new boundary estimate, a new information inequality, a global coupling of block replicas, a plethysm calculation, or any unresolved entropy optimization. Source126's stabilizer/dimension/compression/containment proof then pays the rest with elementary q-block substitutions. The assessment is not based on failure to find an identical theorem title.

## Operative inputs actually read

The pinned source is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, stipulated true. Its full `sections/matching-smoothing.tex` was read, not merely its theorem statement: [selected local source](private/source126/sections/matching-smoothing.tex), canonical manuscript *Exponential PSD rank of positively shifted matching matrices*, `thm:matching-smoothing`, `smooth:lem-fourth-moment`, `smooth:lem-dimension`, and `smooth:eq-containment`. The selected file's Git blob and size match the complete pinned tree. That theorem already includes rare tables and arbitrary positive cell sizes for q=2. Its alternating-cycle proof is a particular way of obtaining the needed trace estimate, rather than a restriction on which classical entropy proof can replace it.

For the new-moment comparison, the operative primary bodies are Csiszar, *The Method of Types* (1998), Section II, Lemmas II.1-II.3 and their proofs, printed pages 2506-2507 (both pages rendered and read), and Bhattacharyya-Gayen-Price-Vinodchandran, [arXiv:2011.04144v1](https://arxiv.org/pdf/2011.04144v1), Lemma 3.3, Corollary 3.4, and the complete Appendix A proof. The former gives finite, uniform type-class bounds; the latter gives the tree-projection KL identity for arbitrary input distributions. The tree-structured hypothesis of the paper's statistical-learning results is not a hypothesis of this identity. The original 1968 Chow-Liu PDF was attempted and returned HTTP403; its body is not claimed read.

For the remaining composition, Source126's actual proof is stronger and more directly applicable than a bare appeal to quasirandomness. Gowers, [0710.3877v1](https://arxiv.org/pdf/0710.3877v1), Lemma 3.2 proof, independently supplies the large invariant top singular-space argument. Vershik-Okounkov, [math/0503040v3](https://arxiv.org/pdf/math/0503040v3), Theorem 5.8, Section 6, Corollary 7.1 and the displayed proofs supply branching and tableau dimensions.

The general hypermatching antecedents were followed in actual bodies: Filmus-Lindzey, [2201.02887v1](https://arxiv.org/pdf/2201.02887v1), Section 9 through the derivation of Proposition 22 and subsequent eigenvalue discussion; Meagher-Shirazi-Stevens, [2108.07692v1](https://arxiv.org/pdf/2108.07692v1), Section 5's meet-table counting proof and Section 6's trace/multiplicity proof. They prevent assuming multiplicity-freeness or confusing their dense partial-derangement operator with every rare conditional table channel. They are not being credited with an unstated all-table moment theorem. The complete direct reduction below makes such a theorem unnecessary for this grade.

## Direct classical derivation of the all-table moment

Use the frozen notation N=qh and let L=ell. Put a=m(q,L), b=m(q,L^2). All entropies use natural logarithms with 0log0=0.

For any finite alphabet of r symbols and any type u=(u_j) of length n, the literal type-class inequalities are

    (n+1)^(-r) exp(n H(u/n))
      <= n! / product_j u_j! <= exp(n H(u/n)).             (1)

These are uniform over all integer types, not only types in the interior. Csiszar Lemmas II.1-II.2 give the stronger lower factor inverse to the exact number of types; (1) merely uses that this number is at most (n+1)^r. The proof bounds the largest type probability under its own empirical product law. Zero symbols can be omitted; the same coarser factor remains valid. This is precisely why no asymptotic Stirling remainder, lower probability cutoff, or minimum cell-size assumption is needed here.

Fix a block table v on r vertex colors, with h blocks and vertex counts n_j=sum_beta beta_j v_beta. For a fixed block partition the number of vertex colorings with that table is exactly

    D(v) = h! / product_beta v_beta!
           * product_beta binomial(q;beta)^(v_beta).

Define the exchangeable block-word law P_v on [r]^q by assigning mass

    (v_beta/h) / binomial(q;beta)

to each word of composition beta. Its coordinate marginal is pi_j=n_j/N and

    H(P_v) = H(v/h) + sum_beta (v_beta/h) log binomial(q;beta).

Apply (1) to the alphabet of block compositions, whose size is m(q,r), and multiply by the exact within-block multiplicities. Also apply (1) to the vertex-color alphabet. This gives the completely finite bounds

    (h+1)^(-m(q,r)) exp(h H(P_v)) <= D(v) <= exp(h H(P_v)),
    (N+1)^(-r) exp(N H(pi)) <= Z(n) <= exp(N H(pi)),       (2)

where Z(n)=N!/product_j n_j!. Counting incidences and vertex-permutation transitivity give the exact table probability p_v=D(v)/Z(n). Feasibility of every admissible table follows by allocating the required distinct vertices to its list of block compositions. Hence no division below is by a zero conditioning probability.

For the prescribed t, write P=P_t, pi=s/N, and p=D(t)/Z(s). In particular

    p >= (h+1)^(-a) exp(h H(P)-N H(pi)).                  (3)

For two vertex colorings z,z' of sizes s, let R be their empirical pair-color distribution and let b_t(z,z') be the probability that a uniform block partition has table t at both. Treat (z,z') as a coloring on L^2 symbols. A compatible pair-color block table v has collapsed tables t,t, vertex counts NR, and an exchangeable word law Q on ([L]^2)^q. Under the identification with a pair of ordered q-tuples, Q has both tuple marginals P and first-coordinate pair marginal R. This follows just by collapsing color compositions and by the simultaneous permutation symmetry of the q positions. It is not a new probabilistic extension theorem.

There are at most (h+1)^b such v; their events are disjoint and (2) applies to each. If the pair incidence is nonzero, take a maximizing H(Q) among the finite compatible tables. Then

    b_t(z,z') <= (h+1)^b (N+1)^(L^2)
                 exp(h H(Q)-N H(R)).                    (4)

The density kernel k of A_Z=T_t T_t^* relative to uniform probability on Z is exactly b_t/p^2, because the table incidence is biregular. From (3)-(4), putting

    I(R)=2H(pi)-H(R),  J(Q)=2H(P)-H(Q),

we obtain

    k(z,z') <= (N+1)^(b+L^2+2a)
               exp(N [ I(R)-J(Q)/q ]).                  (5)

This is the full rare-table normalization; no loss depending on p has been discarded. Classical data processing under the two coordinate projections gives J(Q)>=I(R). It can also be seen directly by expanding I(A_1,A_rest;B_1,B_rest) with the chain rule: the difference from I(A_1;B_1) is a sum of conditional mutual informations. Consequently, without retaining any selected Q,

    k(z,z') <= (N+1)^(b+L^2+2a)
               exp(N (1-1/q) I(R)).                    (6)

Zero pair incidences satisfy (6) as well. This pointwise bound eliminates any question of simultaneous compatibility of maximizers on distinct cycle edges.

The ordinary trace is

    tr(A_Z^q) = |Z|^(-q) sum_(z_1,...,z_q)
                         product_i k(z_i,z_(i+1)),       (7)

with cyclic indices. The factor |Z|^(-q) is essential: matrix entries are k/|Z|. Nonzero eigenvalues of A_Z and T_t^*T_t agree, including multiplicities.

For a joint vertex type Gamma on [L]^q, all coordinate marginals are pi, the exact number of coloring tuples is N!/product_x (N Gamma_x)!, and (1)-(2) give

    number_of_tuples / |Z|^q
       <= (N+1)^(qL) exp(-N TC(Gamma)),
    TC(Gamma)=qH(pi)-H(Gamma).                           (8)

There are at most (N+1)^(L^q) such joint types. Its successive pair marginals are R_i.

For each edge j of the q-cycle remove it to form a spanning path F_j. Let Gamma_Fj be the tree distribution with Gamma's singleton and F_j edge marginals. Rooting the path defines it by the usual product of conditional distributions; arbitrary definitions on zero-probability parent states have no effect. It is normalized, and it is positive on the support of Gamma, so the following relative entropy is finite. The primary tree-projection identity reads

    D(Gamma || Gamma_Fj) = TC(Gamma) - sum_(i!=j) I(R_i).

Average it over j. This yields exactly

    TC(Gamma) - (1-1/q) sum_i I(R_i)
       = (1/q) sum_j D(Gamma || Gamma_Fj) >= 0.           (9)

Combining (6), (8), and (9), every joint-type contribution to (7) is at most

    (N+1)^[qL+q(b+L^2+2a)].

Summing the joint types proves tr((T_t^*T_t)^q)<=(N+1)^E with the E stated above. Since E=C-1-3q<C, N+1>=1 and exp(C)>=1, conclusion 1 with the exact frozen C follows. This derivation is valid for each finite admissible parameter set, including L=1. It does not change the frozen constants or propose the stronger bound as a different nominee.

The author exponent itself has the particularly explicit classical certificate

    -TC + sum_i I(R_i) - (1/q)sum_i J(Q_i)
      = -(1/q)sum_j D(Gamma || Gamma_Fj)
        -(1/q)sum_i [J(Q_i)-I(R_i)] <= 0.                (10)

Thus the purported cancellation is a literal positive average of already paid inequalities. Neither a strengthened data-processing constant nor a new entropy region is needed. This is the operative reason for the grade, rather than the uninformative observation that the individual ingredients have classical names.

## Completion at the exact frozen downstream scope

The source's representation/compression mechanism remains compatible with q-block partitions as follows. Fix d vertices A and let G=S_(N-d) fix them. G-orbits are exactly the equivalence relations on A induced by belonging to a common block (with classes of size at most q). Outside vertices of corresponding blocks can be aligned, followed by all untouched blocks. The pair co-membership indicator is

    b_ij = sum_(e containing i,j; |e|=q) x_e.

Products of b_ij or (1-b_ij) specify an orbit. Upon expansion, repeated x_e are idempotent and distinct intersecting blocks give zero. Each surviving distinct block contains at least two fixed vertices, so each monomial uses at most floor(d/2) blocks. All G-fixed functions therefore lie in P_d. This supplies the exact q-block hypothesis needed by the source dimension argument; no assumption about multiplicities in the hypermatching representation enters.

Branching excludes first rows of length at least N-d from P_d^perp. First columns that long would supply a G-sign vector, but N>qd ensures a block entirely outside A in every partition; a transposition inside that block fixes the partition and negates such a function. It must vanish. For all remaining diagrams, transpose if necessary to put a row of length b>=sqrt(N)>=2d on top. Keep it and d lower boxes. The source tableau construction yields binomial(b,d)>=N^(d/2)/(2^d d!) standard tableaux, and each extends along a fixed corner-addition chain. Thus every nonzero invariant subspace of P_d^perp has dimension at least

    c_d N^(d/2),  c_d=1/(2^d d!),

whenever N>=max(4d^2,qd+1).

Let Q=I-Pi_d and A=T_t^*T_t. The compression B=QAQ is positive, equivariant and has norm ||T_t Q||^2. The min-max characterization implies each ordered compression eigenvalue is no greater than the corresponding eigenvalue of A, hence tr(B^q)<=tr(A^q); commutation of A and Q is unnecessary. Its largest eigenspace, if nonzero, is an invariant subspace of P_d^perp. Using the frozen, weaker moment already implied above,

    c_d N^(d/2) ||T_t Q||^(2q) <= exp(C)(N+1)^C.

For exactly d=ceil(2C+4qK+2), d/2>=C+2qK+1. For exactly the stated N0, N>=exp(C)2^(C+d)d!, so

    ||T_t Q||^(2q)
       <= exp(C)2^(C+d)d! N^(-2qK-1) <= N^(-2qK).

This is conclusion 2 with its original quantifiers and constants, including arbitrary functions and all tables. Zero complement or zero compression causes no exception. Complexification preserves the real operator norm.

Finally fix any d>=0, z, and a block-indicator product. Remove repetitions; intersecting distinct specified blocks make it identically zero. Otherwise let m_alpha be its disjoint block-type counts and a_u=sum_alpha alpha_u m_alpha. Cell-preserving permutation transitivity gives exactly

    E[product_(e in E) x_e | t,z]
      = product_alpha [(t_alpha)_(m_alpha)
                         (product_u alpha_u!)^(m_alpha)]
        / product_u (s_u)_(a_u).                        (11)

The denominator counts injective endpoint lists, is positive because the endpoints exist in z, and is independent of t. The numerator chooses distinct destination blocks and their within-cell bijections. It has total degree sum m_alpha<=d and vanishes for insufficient t_alpha. Choosing an expansion of Pi_d f once, independently of t, and summing (11) supplies one polynomial for all admissible tables. This also handles d=0, every finite N, and arbitrary nonsymmetric f. This is the direct q-block form of `smooth:eq-containment`; it pays conclusion 3 without an extra interpolation or compatibility problem.

## Contribution judgment and its boundaries

This is a useful extension of the source's particular q=2 moment argument. The technical judgment is not that q=2's alternating cycles can be reused unchanged, or that the frozen theorem was located verbatim in another paper. The substantive test is whether its additional operation requires more than a compatible known composition. Here the complete computation (1)-(10) supplies that composition at the actual hypotheses and with stronger finite constants. The block-word lift is the standard multinomial unfolding of an unordered type; the p^(-2) conditioning factors cancel through two exact incidence counts; projection contracts information; and the vector with weight (q-1)/q on each cycle edge is the average of the q spanning paths. The trace expansion dictates precisely those pairs and that cycle. There is no remaining entropy estimate to invent or optimize.

Possible objections have concrete answers. Rare tables do not require lower bounds on p because (3) is relative to its own entropy and is uniform. Zero frequencies do not require continuity arguments. Independently maximizing edge tables need not fit a global law because (6) discards Q before the cycle is considered. Noncommutativity of the hypermatching coherent configuration does not obstruct invariant top eigenspaces or orthogonal compression. The failed second moment demonstrates a limitation of one route, not that using a sufficiently high moment is a nonroutine operation. Exact large constants, proof length and the parameter q>=3 do not supply contribution evidence.

Filmus-Lindzey's actual Section 9 derives the (N-2,2) projection/eigenvalue for the noncommutative orbital algebra, rather than controlling every high-degree rare channel. Meagher-Shirazi-Stevens use a positive-density graph and an ordinary second trace; their degree asymptotic cannot be substituted for (3)-(6). These limitations do not support SUBSTANTIAL, because the primary type/tree proofs together with Source126 do give the full direct reduction. The imported Bender enumeration proof was not read and is not a premise of this review's derivation.

The exact original I199/I202 fixtures were read fully on the representation overlap. They concern the fixed canonical (7,8) map, an actual deficiency module, determinant-socle multiplication, and unresolved full-map obligations. This review neither changes their scopes/dispositions nor treats this table-channel upper bound as a result about their strict positivity/injectivity problem. No approximate-rank target was reopened.

The literature search and reading are bounded, not exhaustive. A title-identical antecedent is not asserted absent, and priority is not assessed. The verdict instead rests on the complete standard-operation derivation written above. No identified missing research is required for that conditional contribution conclusion. Precise reading extents, unneeded unread antecedents, access failure, truncation recovery and the corrected temporary write-location incident are in [the reading and isolation record](notes/02-reading-and-isolation.md). Artifact controls establish only file integrity.
