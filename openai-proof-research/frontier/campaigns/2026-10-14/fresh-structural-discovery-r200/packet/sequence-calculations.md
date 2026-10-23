# R200 sequence calculations — prefreeze working derivation, not a nominee

These calculations use the actual September 26 Source324 construction, denoted B, with all operative proofs stipulated true at the pinned revision. They change its completed norm. They do not claim the new norm is equivalent to the old one. They do not settle the original I88 S88 target. No correctness, contribution, acceptance, or count is assigned.

## 1. Exact modified object and preservation of the metric construction

Use B's real spaces D=E⊕∞U, E=c0(N), U=c0(⊔Γλ), closed unit ball B_D, correction coordinates fγ, finite-coordinate sets Iγ, and exactly its classes T_h and V_h. Preserve the nonincreasing dyadic scales and strict sum of scales <ℓ_j/2, and preserve the tail-factor restrictions. The triple set consists of d=(L,C,p), L in the source's countable class list, C a positive integer, p=1+1/k, k≥1. A finite list (uν) from L is C-admissible if every signed sum has Lipschitz constant ≤C on B_D. Equivalently,

    Σν |uν(s)−uν(t)| ≤ C ||s−t||_D.

Let M0 be the real mass-zero finite molecules on B_D. Let σ_d be B's exact supremum of the ℓ_p norms of list evaluations. Enumerate all triples once, choosing d0=(T_1,5,2) first; enumerate the rest in any fixed bijection with integers ≥2. Define

    β_d = 2^(−d)/C_d,
    N1(m) = Σ_d β_d σ_d(m),
    N = {m:σ_d(m)=0 for every d},
    Z1 = completion of M0/N in N1.

No labels or parameter budgets in the tests have changed. All β_d are positive and Σβ_d C_d=1. For a molecule m=Σ_s a_s(δ_s−δ_0),

    σ_d(m) ≤ C_d Σ_s |a_s| ||s||,
    N1(δ_s−δ_t) ≤ ||s−t||.

Thus N1 is a finite seminorm with kernel exactly N. It gives a Banach completion and a 1-Lipschitz map ζ1(s)=[δ_s−δ_0]. Since B_D is separable and molecules have finite support, rational combinations of ζ1 on a countable dense subset are dense. Hence Z1 is separable and real.

Here is the exact completed-norm justification, avoiding interchange of an uncontrolled infinite sum. Let X_d be the completion of M0/ker σ_d with its σ_d norm. The linear map

    J(m)=(β_d [m]_d)_d in (⊕_d X_d)_1

is isometric for N1 and has kernel N. Extend it as an isometry J:Z1→(⊕X_d)_1. Each coordinate has norm β_d σ_d on molecules, extends continuously, and determines the extended seminorm σ_d. Thus

    ||z||_Z1 = Σ_d β_d σ_d(z)                         (1)

for every z in the completion. The range of J is closed because Z1 is complete. We do not assert it is the entire outer sum.

For a fixed class L, choose an integer C_L at least its actual global Lipschitz bound. A singleton is admissible for d_L=(L,C_L,2), so

    |<u,z>| ≤ β_(d_L)^(−1) ||z||,   u in L.           (2)

For a fixed d and admissible list, its evaluation operator into finite-dimensional ℓ_p has norm ≤β_d^−1. The supremum of all these operators' norms on z defines a β_d^−1-Lipschitz seminorm agreeing with σ_d on dense molecules. Therefore B's exact list formula continues to hold on Z1.

If u_n from one fixed class converges pointwise to u, the molecule evaluations converge. Bound (2) makes u a bounded functional and, for each fixed z and any molecule m,

    |<u_n−u,z>| ≤ |<u_n−u,m>| + 2β_(d_L)^−1 ||z−m||. (3)

Taking m close to z and then n large proves convergence on that fixed vector. This is precisely the order needed by every source tail cut and plateau modification. It does not assert uniform convergence on a moving sequence of z's.

The source correction h(s)=(S_s−P)s is U-valued. Define Q1m=Σ_s a_s h(s). All fγ belong to T_1 and Lip(fγ)≤4+12/1000<5, whence

    ||Q1m||_U ≤ σ_(T_1,5,2)(m) ≤ 10 N1(m).

The constant is 10 since β_1=1/10. Q1 annihilates N and extends into complete U, with ||Q1||≤10. Define on all D

    K1(0)=0,
    K1(x)=||x|| ζ1(x/||x||), x≠0.

The source radial estimate applies verbatim because ζ1 is 1-Lipschitz and zero-preserving: Lip(K1)≤3, ||K1(x)||≤||x||. The identity on point molecules gives exactly

    Q1K1=g−P.

The already constructed g is onto with lower c_g=22/125 and upper 628/125. Consequently the source absorption lemma, now with this actual Q1 and K1, gives

    F1:Z1⊕∞c0→Z1,  F1(b,t)=b+K1(t,Q1b),
    G1(d)=(d−K1(t_d,u_d),t_d), (t_d,u_d)=g^−1(Q1d).

To check compatibility explicitly, Q1F1(b,t)=g(t,Q1b), so G1F1=(b,t). In the other direction Q1(d−K1(t_d,u_d))=u_d, so F1G1=d. All arguments belong to the displayed complete spaces. No section of Q1, linear or Lipschitz, is supplied or needed.

The global constants are

    Lip(F1) ≤ 1+3 max{1,10}=31,
    Lip(G1) ≤ max{1+30/(22/125),10/(22/125)}=1886/11.

Thus, for every a,a' in Z1⊕∞c0,

    (11/1886)||a−a'|| ≤ ||F1(a)−F1(a')|| ≤31||a−a'||. (4)

F1 and G1 fix zero and are positively homogeneous. Positive homogeneity means nonnegative real scaling; oddness and complex homogeneity are not inferred. These are onto global bounds, not local/coarse bounds.

## 2. A fixed seminorm detects a weakly null sequence

Let (z_n) be weakly null in Z1 with r≤||z_n||≤M, r>0. Suppose for contradiction that σ_d(z_n)→0 for every fixed d. Then Jz_n is weakly null in the outer ℓ1 sum, its norm is at least r, and each coordinate norm tends to zero.

Choose an error ε with 0<ε<r/4. By a successive head/tail selection choose n_j and disjoint finite intervals A_j of d-indices such that

    ||Jz_(n_j)−w_j||_ℓ1 < ε,
    w_j = 1_(A_j) Jz_(n_j),
    ||w_j|| > r−ε.

Indeed, after the preceding endpoint is fixed, finitely many coordinate norms tend to zero, so their sum is <ε/2 for a sufficiently late n_j. Then the tail of that fixed Jz_(n_j) has sum <ε/2 beyond a new endpoint. For each finite interval A_j, choose norm-one functionals on its finitely many coordinate spaces, with signs arranged so their sum evaluates w_j to ||w_j||. Hahn–Banach supplies those norming functionals. Combine them on disjoint A_j, using zero outside their union. The resulting functional φ on the outer ℓ1 sum has norm at most 1. Hence

    φ(Jz_(n_j)) ≥ ||w_j||−ε > r−2ε > r/2.

This contradicts weak nullity. Thus a fixed d=(L,C,p) has σ_d(z_n)≥a>0 along a subsequence. This is the extra conclusion that the source's outer ℓ2 argument did not give for arbitrary weakly null sequences. The proof is the standard disjoint-block property of an ℓ1 sum; no new compactness principle is assumed.

Choose a listed p'<p with the same L,C, writing d' for that triple. Bound (1) gives σ_d'(z_n)≤β_d'^−1 M=:B0. Choose d-admissible lists whose ℓ_p evaluations are at least a/2. The same list is d'-admissible. If its evaluations have absolute values xν, then

    (a/2)^p ≤ Σ xν^p ≤ (max xν)^(p−p') B0^p'.

Thus a scalar test H_n in one fixed L has |<H_n,z_n>|≥δ, where

    δ=((a/2)^p/B0^p')^(1/(p−p')) >0.              (5)

This is exactly the source exponent interpolation, now after the ℓ1-sum selection.

## 3. Source compatible-detector selection survives unchanged

Apply B, Proposition `prop:compatible-detectors`, using the completion facts above rather than B's original outer ℓ2 norm. Its geometric argument has no other dependence on that outer norm:

* Distinct labels in bounded bands: the radii depend on coordinates escaping every finite set. Support requires τ_(M_n)≥c_*>0. For each fixed z_n, (3) permits a tail cutoff b_(c,N_n), chosen after n is fixed. A subsequence has disjoint supports in one enlarged V_H.
* Distinct labels with bands tending to infinity: tags have coordinatewise-convergent subsequences. The strict scale budget permits a final G-operation after each fixed z_n is chosen. Support concentration puts later supports inside earlier plateau cylinders. One fixed enlarged T_(h+1) gives the common signed Lipschitz bound.
* One repeated label: expand every varying G as Id+R and each escaping tail factor b as 1+(b−1), with parameters fixed before expansion. Fixed terms pair to zero by weak nullity. A retained varying term either has escaping tail support, or its first small R has sup norm O(ε_n) and projected support radius O(ε_n). Nonincreasing scales preserve this after all later operations. A final small G and recursive nesting make plateau values summable. These are the original support calculations and the original fixed-vector limit, with only the numerical dual bounds in (3) changed.

Consequently, after taking a subsequence there are a single class L1, a fixed integer C1, tests H_n in L1, and δ1>0 such that

    |<H_n,z_n>|≥δ1,
    Lip(Σ_(n∈A) e_n H_n)≤C1

for every finite A and signs. No uniform bound independent of the original weakly null sequence is claimed.

For every listed p>1, the same compatible infinite list defines a bounded linear map

    T_p:Z1→ℓ_p,   T_p z=(<H_n,z>)_n,
    ||T_p||≤β_(L1,C1,p)^−1.                         (6)

This follows by the exact finite-list formula and monotone limits of finite sums of nonnegative p-th powers. In particular <H_n,z>→0 for each fixed z, using p=2. This is stronger than having only uniform individual dual norms.

## 4. One subsequence works for every exponent greater than one

There is an elementary simultaneous diagonal selection; no changing-exponent limit is needed. Recursively choose indices n_j so that for all i<j,

    |<H_(n_i),z_(n_j)>| ≤ δ1 2^(−i−j−4),
    |<H_(n_j),z_(n_i)>| ≤ δ1 2^(−i−j−4).             (7)

The first inequality uses weak nullity and finitely many old bounded functionals. The second uses the pointwise-null property deduced from (6), on finitely many fixed old vectors. Both permit the same sufficiently late n_j. The diagonal evaluations remain ≥δ1 in absolute value.

For a finitely supported scalar sequence a, put z=Σ_i a_i z_(n_i). Evaluation by the selected tests gives the matrix M=D+R, with D diagonal, |D_ii|≥δ1, and |R_ji|≤δ1 2^(−i−j−4). For every 1≤p<∞, Hölder's inequality and the geometric sums yield

    ||Ra||_p ≤ (δ1/16) ||(2^(−j))_j||_p
                         ||(2^(−i))_i||_(p') ||a||_p
             ≤ (δ1/16)||a||_p.

For p=1 use the ℓ∞ norm on the second geometric sequence; the same bound suffices. Both geometric norms are ≤1 for exponents in [1,∞]. Hence

    ||Ma||_p ≥ (15δ1/16)||a||_p.                    (8)

For every listed p, (6) and (8) imply

    ||Σ_i a_i z_(n_i)|| ≥ (15δ1/16) β_(L1,C1,p)||a||_p. (9)

For any real exponent q>1, select a listed p with 1<p≤q. Since ||a||_p≥||a||_q, the same inequality supplies a positive c_q for q. Thus this single subsequence dominates the ℓ_q basis for every q>1. The constants depend on q and the original sequence; neither their infimum as q↓1 nor an ℓ1 lower estimate is asserted. Boundedness of z_n only gives the upper estimate M||a||_1.

This proves a full sequence property for this modified completed space. In particular no bounded below linear T:ℓ_q→Z1 exists for any 1<q<∞: the unit basis images are seminormalized and weakly null, so (9) at any listed p<q would give c_p N^(1/p)≤||T||N^(1/q), impossible for large N. The same argument excludes T:c0→Z1, since its unit-vector sums have norm 1. Closed range is implicit in being bounded below; complemented embeddings and quotients are not being conflated with copies.

More generally, if a seminormalized weakly null sequence (x_n) in a Banach space X obeys

    E||Σ_(j=1)^N ε_j x_(n_j)|| ≤ A N^α, α<1,

uniformly over its subsequences, then it cannot have a bounded below image in Z1. Equation (9), applied to every sign choice and p with 1/p>α, gives the incompatible lower bound c_p N^(1/p). This statement needs no appeal to a type theorem. We do not infer a blanket property of every space of nontrivial type without stating the separate weak-sequence extraction input.

Restricting (4) to {0}⊕c0 embeds c0 bi-Lipschitzly in this same Z1. Applying the source's already-paid Aharoni composition makes it metrically universal. That universality is a source transfer and is not a new operation. There is no assertion that any of the maps is a linear splitting, that Z1 is Schur, has AP, is reflexive, is a dual, has the Radon–Nikodym property, or has finite cotype.

## 5. Strongest-reduction assessment before any campaign freeze

The closed calculation is: replace the outer ℓ2 aggregation by ℓ1, repeat the source's norm completion and fixed-class duality with explicit changed constants, invoke its already-paid full geometric selector, and use a standard two-sided matrix diagonalization. The changes genuinely define a different normed completion, but the steps above exhibit the whole reduction; a new norm is not by itself a substantial contribution. This round has not isolated a nonroutine operation beyond those paid source and classical steps. Therefore these calculations are retained without selecting them as the requested substantial nominee.

The remaining attractive endpoint would require a stronger construction with the Schur property, while preserving the same global absorption identity. The next working note tests the exact most obvious endpoint and proves that it fails, rather than treating missing scalar extraction as evidence of impossibility of all constructions.

## 6. Stronger operator consequence of the same paid reduction

The sequence property gives more than nonembedding of classical sequence spaces. Every bounded linear operator T:X→Z1 from a real Banach space with Rademacher type r>1 is completely continuous. Here the hypothesis means there is a finite constant A such that

    (E||Σ ε_j x_j||^r)^(1/r) ≤ A (Σ||x_j||^r)^(1/r)

for every finite family in X. If x_n→0 weakly but ||Tx_n|| does not tend to zero, pass to a subsequence bounded below in image norm; boundedness of x_n follows from uniform boundedness. The sequence result supplies a further subsequence and a listed p<r with

    ||Σ_(j=1)^N ε_j Tx_(n_j)|| ≥ c_p N^(1/p)

for every sign choice. On the other hand, the displayed type inequality and Jensen give

    E||Σ_(j=1)^N ε_j Tx_(n_j)|| ≤ ||T|| A (sup_n||x_n||) N^(1/r).

The incompatible powers prove complete continuity. This proof uses the type inequality itself and avoids importing an unstated theorem extracting weakly null sequences in arbitrary spaces.

For completeness, all bounded operators T:ℓ_q→Z1, 1<q<∞, are compact by a direct sequence proof that does not need a type classification. A bounded sequence in ℓ_q has, after diagonal selection, a coordinatewise limit x with finite ℓ_q norm (Fatou). Boundedness and density of finitely supported vectors in ℓ_(q') show weak convergence to x. If its T-images fail to have a norm-convergent subsequence, a subsequence of y_n=x_n−x has ||Ty_n|| bounded below. The weakly null bounded y_n admit disjoint finite-coordinate blocks v_j with ||y_(n_j)−v_j||≤2^(−j). This follows by choosing a small finite head before each vector and a small tail after it. Then for every N and every signs,

    ||Σ_(j=1)^N ε_j y_(n_j)||_q ≤ (sup_j||v_j||)N^(1/q)+1.

The image subsequence property at a listed p<q contradicts this bound. Therefore T sends every bounded sequence to one with a norm-convergent subsequence, which is compactness. This is again a consequence of the same norm modification and diagonal argument, not a separate campaign nomination.
