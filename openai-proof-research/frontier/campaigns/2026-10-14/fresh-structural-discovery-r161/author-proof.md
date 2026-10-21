# Author proof at the frozen r161 scope

This is discovery-stage original proof prose for `scope-frozen.md`, SHA256 b5c7b51d352e250df511fae5d3456ccbaa2756180111020b3108415c12a7d813. It is not an independently reviewed proof, contribution grade, manuscript, formal artifact or release. The pinned input and operative proofs are stipulated true. No change to any old scope or disposition is proposed.

## 1. Definitions and the strongest paid inputs

Fix integers q>=3, ell>=1 and N=qh>0. Let X be the unordered partitions of [N] into h blocks of size q. Let Z be the ordered partitions into positive cell sizes s=(s_1,...,s_ell), sum s_u=N. Both carry uniform probability. We identify Z with colorings z:[N]->[ell] with those color multiplicities. Put

    A(q,r)={alpha in Z_{>=0}^r: sum alpha_u=q},
    m(q,r)=|A(q,r)|=binomial(q+r-1,r-1).

A table t=(t_alpha) has nonnegative integer entries, sum t_alpha=h and sum alpha_u t_alpha=s_u. A block partition M has this table at z when exactly t_alpha of its blocks have color composition alpha. All such tables are feasible: allocate alpha_u distinct vertices of color u to every block of each required type. The balance equations use every vertex exactly once. For fixed z, T_t averages f(M) uniformly over these M. P_d is the span of products of at most d full-block indicators x_e(M)=1_{e in M}, and Pi_d is its uniform orthogonal projection.

Source126, `sections/matching-smoothing.tex`, `thm:matching-smoothing` and `smooth:eq-containment`, gives this entire package for q=2, including rare tables and unbalanced cell sizes. Its proof uses a polynomial fourth moment, a fixed-vertex stabilizer argument, Young-diagram dimension bounds, equivariant compression and a containment formula. This proof retains the last four operations with their required q-block compatibility checked below. It replaces the fourth moment with a qth moment of T_t^*T_t. It does not transfer the main PSD-rank conclusion.

The entropy tools are classical. Type-class counting and uniform polynomial errors are the method of types (Csiszar1998, SectionII, LemmasII.1–II.3, including proofs). The tree entropy inequality follows from the tree projection identity of Chow–Liu; an actual accessible proof was read in Bhattacharyya–Gayen–Price–Vinodchandran, arXiv:2011.04144v1, Lemma3.3, Corollary3.4 and AppendixA. Original Chow–Liu1968 retrieval failed. We prove all entropy inequalities used here directly, including at zero probabilities. Symmetric-group branching and tableau dimensions use Vershik–Okounkov, arXiv:math/0503040v3, Theorem5.8, Section6 and Corollary7.1. No plethysm multiplicity formula or Foulkes injectivity assertion is needed.

## 2. Exact type counts, uniformly at the boundary

We will permit zero color-class sizes in auxiliary joint colorings. For a table v=(v_beta) on r colors, let n_j=sum_beta beta_j v_beta, with sum v_beta=h and sum n_j=N. Set

    D(v)=h!/prod_beta v_beta! * prod_beta (q!/prod_j beta_j!)^{v_beta},
    Z(n)=N!/prod_j n_j!.

For a fixed block partition M, D(v) is the exact number of colorings with table v: assign types to the h distinct blocks, then assign the colors within each block. For a fixed coloring with multiplicities n, double counting incidences and transitivity under S_N show

    Pr_{M uniform in X}[table v at that coloring] = D(v)/Z(n).       (2.1)

This also proves that every row and every column of the table-incidence matrix has the same respective degree. Zero n_j or v_beta are harmless, with 0!=1.

Associate to v an exchangeable probability law P_v on [r]^q: for a word w of composition beta,

    P_v(w)=(v_beta/h)/binomial(q;beta).

Its one-coordinate marginal is pi_j=n_j/N. Its entropy, using natural logarithms and 0log0=0, is

    H(P_v)=H((v_beta/h)_beta)+sum_beta(v_beta/h)log binomial(q;beta).

For j>=1 put R_j=log(j!)-jlog j+j and R_0=0. Integral comparison of the increasing function log x gives

    0<=R_j<=1+log(j+1).

With U=1+log(N+1), direct substitution into the exact factorials gives

    log D(v) = h H(P_v)+R_h-sum_beta R_{v_beta},
    log Z(n) = N H(pi)+R_N-sum_j R_{n_j}.                 (2.2)

Consequently

    -(m(q,r)+1)U
      <= log(D(v)/Z(n))-[hH(P_v)-NH(pi)]
      <= (r+1)U.                                       (2.3)

There is no assumption that a positive entry stays bounded away from zero, and there is no division by a zero frequency. In particular these are uniform estimates for rare tables.

For our fixed table t, write P=P_t, pi=s/N and p=D(t)/Z(s)>0. For two colorings z,z' with the given s, let R be their empirical joint color law on [ell]^2. Denote by

    b(z,z')=Pr_M[table t at z AND table t at z'].

To count this probability, regard each vertex as colored by its pair (z(v),z'(v)). A joint block table v on r=ell^2 pair colors is compatible precisely when its two collapsed block-type tables are t and its vertex counts are NR. There are at most (h+1)^{m(q,ell^2)} possible v. By (2.1), b is the sum of D(v)/Z(NR) over exactly these v; the events are disjoint. Let Q=P_v be the corresponding law on ([ell]^2)^q, equivalently a law of two ordered q-tuples (A_1,...,A_q) and (B_1,...,B_q). Its tuple marginals are exactly P,P, and its first-coordinate pair marginal is R. Indeed the law is invariant under simultaneous permutations of the q positions, its collapsed composition distribution is t/h, and its expected composition is NR/h. These observations also verify all normalizations in the auxiliary joint-table count.

If b>0, choose a compatible v maximizing H(Q). Applying (2.3) with r=ell^2 and summing the number of possible tables gives

    b(z,z') <= exp(hH(Q)-NH(R)+B U),
    B=m(q,ell^2)+ell^2+1.                              (2.4)

The choice of Q may depend on R. No joint consistency among the maximizing Q's on different edges will be assumed or needed.

## 3. The replica entropy inequality

Here is the entropy calculation which replaces the alternating-cycle count in Source126.

Let Gamma be any probability distribution of (Z_1,...,Z_q), all with marginal pi, and let R_i be the distribution of (Z_i,Z_{i+1}), with indices cyclic. For each i suppose Q_i is any law of a pair of q-tuples with tuple marginals P,P and first-coordinate pair marginal R_i. Define

    I_i=I(Z_i;Z_{i+1})=2H(pi)-H(R_i),
    J_i=I(A_1,...,A_q;B_1,...,B_q)=2H(P)-H(Q_i),
    TC=qH(pi)-H(Gamma).

Then

    -TC+sum_i I_i-(1/q)sum_i J_i <= 0.                 (3.1)

For completeness, nonnegativity of relative entropy follows from log u<=u-1, after restricting to the positive support (infinite cases are nonnegative). This proves nonnegativity of conditional mutual information. The chain rule for mutual information now gives data processing under deleting coordinates: I(A^q;B^q)>=I(A_1;B_1). Thus J_i>=I_i, with no positivity-of-support assumption.

For any spanning tree F on [q], root and order its vertices with parents before children. The entropy chain rule and the fact that conditioning can only decrease entropy give

    H(Gamma)<=H(Z_root)+sum_{v!=root}H(Z_v|Z_parent(v))
              =qH(pi)-sum_{ij in F} I(Z_i;Z_j).

Apply this to each of the q paths obtained by removing one edge from the q-cycle. Each cycle edge is retained q-1 times. Averaging yields

    TC >= ((q-1)/q)sum_i I_i.

Combining with J_i>=I_i proves (3.1). The distribution Gamma need not be tree-structured, the Q_i need not fit into a global block law, and the inequalities remain valid when any probabilities are zero. This is crucial: the independent maximizers used in (2.4) are legitimate.

Equivalently, (3.1) states

    H(Gamma)+qH(pi)-sum_i H(R_i)
       +(1/q)sum_i H(Q_i)-2H(P) <= 0.                 (3.2)

The inequalities themselves are not claimed new. The added construction is to organize the qth operator trace into these vertex and block types so that its complete exponent is exactly (3.2), including all rare-event normalizations.

## 4. Uniform qth moment

All operator traces in this proof are ordinary traces, not traces divided by the dimension. The kernel of T_t relative to the uniform laws is 1_{table=t}/p. The adjoint has the same incidence kernel because its row and column marginals are uniform. Thus A_Z=T_tT_t^* has density kernel

    kappa(z,z')=b(z,z')/p^2

relative to the uniform law on Z. Its ordinary matrix entry is kappa(z,z')/|Z|. For q>=3,

    tr(A_Z^q)=|Z|^{-q} sum_{z_1,...,z_q} prod_i kappa(z_i,z_{i+1}).   (4.1)

This is an exact finite formula. Terms with a zero b are omitted. The nonzero spectra of T_tT_t^* and T_t^*T_t agree with multiplicity, so either qth trace is the same.

Group the tuples (z_1,...,z_q) by their vertex joint type Gamma on [ell]^q. There are at most (N+1)^{ell^q} such types. Each type has exactly N!/prod_gamma(N Gamma_gamma)! tuples. By (2.2), its count divided by |Z|^q is at most

    exp(N[H(Gamma)-qH(pi)]+(1+q*ell)U).                (4.2)

For edge i use its marginal R_i and select a compatible maximizing Q_i as in (2.4). The lower bound in (2.3) for p yields

    kappa(z_i,z_{i+1})
      <= exp(hH(Q_i)-NH(R_i)-2hH(P)+2NH(pi)
             +[B+2(m(q,ell)+1)]U).                    (4.3)

Multiplying (4.2) and the q bounds (4.3), and using h=N/q, makes the coefficient of N exactly the left side of (3.2). It is nonpositive. Set

    C0=1+q*ell+q*(m(q,ell^2)+ell^2+1)+2*q*(m(q,ell)+1),
    C=C0+ell^q.

Every joint-type contribution to (4.1) is at most exp(C0 U). Summing the possible types gives

    tr((T_t^*T_t)^q)
       <= (N+1)^{ell^q} exp(C0 U)
       <= exp(C)(N+1)^C.                              (4.4)

This proves conclusion1 with precisely the constant in the frozen scope. It holds for all allowed N, not only asymptotically. All estimates used integer type counts and uniform factorial remainders; tiny p, zero table entries and small cell sizes introduced no unaccounted losses.

## 5. Dimensions outside the block-product span

We give the compatibility proof rather than assume that a result about perfect matchings automatically applies to q-block partitions. Fix d>=1 and N>=max(4d^2,qd+1). Fix a set A of d vertices, and let G=S_{[N]\A} fix A pointwise.

A G-orbit in X is determined by the equivalence relation on A in which i~j means that i and j belong to the same block. To see sufficiency, align the outside vertices of each block meeting A, then align the remaining blocks and their vertices. Blocks have fixed size q, so these bijections extend to an element of G. Relations with a class of size larger than q never occur and are simply omitted.

For i,j in A put

    b_ij(M)=sum_{e containing i,j, |e|=q} x_e(M).

Exactly one block contains i, so this is the indicator of i~j. An orbit indicator is the product of b_ij over pairs required equivalent and (1-b_ij) over pairs required inequivalent. Expand these finite products and then the displayed sums. Repeated full-block indicators are idempotent; any product containing two distinct intersecting blocks vanishes. In every remaining monomial the distinct blocks are disjoint, and each contains at least two vertices of A. There are therefore at most floor(d/2) such blocks (the weaker bound d suffices). Hence every G-invariant function on X lies in P_d.

Complexify. Every irreducible S_N constituent is indexed by a Young diagram lambda of N. If its first row has length at least N-d, branching down to S_{N-d} contains the trivial representation: remove d corner boxes until a row of length N-d remains. Such a constituent in P_d^perp would supply a nonzero G-fixed vector there, contradicting the preceding paragraph. If the first column has length at least N-d, branching similarly supplies a sign vector for G. But no nonzero function on X transforms by that sign: h=N/q>d ensures that each M has a block completely outside A; a transposition of two vertices of this block belongs to G, fixes M, and would negate the value of a sign-transforming function at M. Its value is zero at every M. Thus both the first row and the first column of every remaining diagram are shorter than N-d.

We now reproduce the source's general tableau lower bound with explicit sufficient thresholds. A diagram's first row length times its first column length is at least N. Transpose if necessary (dimension is unchanged) so that its first row has length b>=sqrt(N)>=2d. There are at least d boxes below that row. Retain the full row and any Young subdiagram of exactly d boxes below it. Put labels1,...,d into the first d positions of the top row. Choose any d labels from d+1,...,b+d for the lower boxes, placing them in a fixed standard order, and put the other labels increasingly into the remaining top-row boxes. Every lower box is in one of the first d columns, so all columns increase. Each of the binomial(b,d) resulting tableaux extends to lambda along a fixed corner-addition chain with larger labels. By the tableau dimension formula,

    dim(lambda)>=binomial(b,d)>=(b/2)^d/d!
                >= c_d N^{d/2},   c_d=1/(2^d d!).      (5.1)

The branching and dimension facts are standard and were read in Vershik–Okounkov. Multiplicity-freeness of the q-block permutation representation is neither true in general nor needed. Filmus–Lindzey Section9 explicitly treats this noncommutative setting. Every nonzero invariant subspace of P_d^perp contains an irreducible constituent and has at least the dimension (5.1).

## 6. Compression gives the frozen norm estimate

Let Q=I-Pi_d and A=T_t^*T_t on L2(X). Both A and Q commute with S_N: the table relation is invariant under simultaneous vertex permutation, and P_d is invariant. The compression B=QAQ on P_d^perp is positive semidefinite and equivariant. We do not assume A and Q commute. Its norm is

    ||B||=||T_tQ||^2.

By the min–max principle, the ordered eigenvalues of an orthogonal compression do not exceed the corresponding eigenvalues of the original PSD operator. Raising the nonnegative eigenvalues to q and summing proves

    tr(B^q)<=tr(A^q).                                  (6.1)

If B is nonzero, its largest-eigenvalue eigenspace is an invariant subspace of P_d^perp. Equations (4.4), (5.1) and (6.1) give

    c_d N^{d/2} ||T_tQ||^{2q} <= exp(C)(N+1)^C.         (6.2)

The same inequality is automatic if B=0, including a zero-dimensional complement. Complexification preserves all norms, eigenvalue multiplicities and traces, so this proves the real estimate as well.

For any K>0 choose exactly the frozen values

    d=ceil(2C+4qK+2),
    N0=ceil(max(4d^2,qd+1,exp(C)*2^{C+d}*d!)).

For N>=N0, we have d/2>=C+2qK+1, (N+1)^C<=2^C N^C and c_d^{-1}=2^d d!. Therefore (6.2) implies

    ||T_tQ||^{2q}
       <= exp(C)*2^{C+d}*d! * N^{-2qK-1}
       <= N^{-2qK}.

Taking the 2qth root proves conclusion2, for every allowed s,t with no change to d or N0.

## 7. The simultaneous polynomial, with exact coefficients

Fix z and a generating product of full-block indicators of degree at most d. Remove repetitions. If two distinct specified q-subsets overlap, the product is identically zero and has zero conditional mean. Otherwise they form a partial block partition E. Let m_alpha count its specified blocks of type alpha at z, and put a_u=sum_alpha alpha_u m_alpha. Since all endpoints are actual distinct vertices in color cell u, a_u<=s_u.

Uniformly permute vertices inside each color cell of any one block partition with table t. The resulting block partition is uniform among all those with table t, by transitivity. Equivalently, take inverse images of the specified endpoints. Their ordered lists are uniform over prod_u(s_u)_{a_u} injective choices. For each type alpha, choose distinct destination blocks in (t_alpha)_{m_alpha} ways. For each chosen block there are prod_u alpha_u! ways to match the specified vertices to its vertices in the corresponding color cells. Thus the exact containment probability is

    E[prod_{e in E} x_e(M) | table t at z]
      = prod_alpha[(t_alpha)_{m_alpha}
                    (prod_u alpha_u!)^{m_alpha}]
        / prod_u(s_u)_{a_u}.                           (7.1)

The denominator is strictly positive and independent of t. The numerator has total degree sum_alpha m_alpha<=d. If some t_alpha<m_alpha the falling factorial is zero, exactly as it should be.

An expansion of Pi_d f in these generating products can be fixed before t is varied. Summing their polynomials (7.1) with the fixed expansion coefficients produces one real polynomial of degree at most d which works at every admissible table. No independence of those spanning products is required. For d=0 the assertion is just constancy. This proves conclusion3 in its entire frozen scope.

## 8. Why the moment order is a genuine extra issue, and what is not claimed

For a balanced two-cell example take N divisible by 2q and let all blocks be monochromatic, with h/2 blocks of each color. Then |Z|=binomial(N,N/2) and D(t)=binomial(h,h/2). Starting from a coloring z, sample a compatible M, then sample a compatible z'. The probability of returning to exactly z is 1/D(t). Thus the diagonal paths in the nonnegative matrix A_Z give, for each positive integer p,

    tr(A_Z^p)>=binomial(N,N/2)/binomial(h,h/2)^p.

For p<q its logarithm is (1-p/q)Nlog2+O_q(logN), so it is exponential. In particular Source126's polynomial fourth-moment estimate (p=2) cannot simply be reused for q>=3. At p=q this particular obstruction disappears, and Sections2–4 prove a bound for ALL tables, not just this monochromatic example. The displayed lower bound is a diagnostic, not an impossibility statement about smoothing or about other methods.

The extra operation offered for contribution review is the boundary-uniform q-replica trace reduction and entropy cancellation in Sections2–4. Stabilizer dimensions, compression and polynomial containment are paid source/classical operations. The type and tree entropy inequalities are classical too. This proof does not certify that their integration is new to the literature or substantial enough for acceptance. Its comparison must be reviewed using the actual primary proofs and the disclosed search limits.

No conclusion is asserted about approximate PSD rank, arbitrary entrywise perturbations, quantum communication, other cones, growing q or ell, Foulkes injectivity, or complexity of generating the polynomial. In particular the old approximate matching-rank target stays rejected and the old fixed-map Foulkes targets retain their exact quantifiers and dispositions. No author-assigned correctness/contribution/acceptance grade or count follows from this document.
