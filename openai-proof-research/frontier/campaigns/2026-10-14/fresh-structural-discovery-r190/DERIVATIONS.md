# r190 — prefreeze derivations: finite detection of cyclic-product stabilization

PREFREEZE research record. No theorem was frozen; this is not an author-proof nominee, an independent review, or a mathematical grade. The whole pinned source, including its operative proofs, is stipulated true. Source text and the primary/original-history interfaces described in INTERFACES.md were read before this extended derivation. The one developed direction is a finite quantitative replacement for the large-cyclic-factor step in the actual proof, retaining an arbitrary embedded subgroup. The reductions below do not replace any old frozen target.

## 1. The exact finite operation under investigation

Fix a prime p, a finite p-group P, H <= P, and k >= 0. Put

    A_r = (Z/p^r)^k,
    d = ell(P,H),   D = d+k,
    f(r) = ell(P x A_r, H x 0).

For k=0, f(r)=d throughout. For k>0 the intended quantitative operation is an a priori, proved finite precision bound R, derived from finite structural data of the embedded pair and k, at which f(R)=D, together with a finite certificate excluding every shorter cyclic subnormal chain. By a bound we mean a controlled expression or proved bounded elimination procedure, not the definition 'the first r where equality holds', or a maximum over unknown stabilization times. The relevant finite structural data may include p, a multiplication table of P, H, log_p|P|, the exponent, and k; a bound depending only on d and k will fail below.

The output would make the source's all-rank-amplification argument finite at a prescribed precision. It would not construct a sharp finite spectrum or bound its cells. I105's full quantitative realization target remains untouched. No extension to a different fixed-point functor or to infinite groups as equivariant symmetry groups is intended. The pro-p groups below are auxiliary algebraic inverse limits only.

## 2. What compactness already gives, including the relative case

Quotienting A_(r+1) onto A_r maps every cyclic subnormal chain to such a chain, possibly with repetitions. Thus f(r) <= f(r+1). Concatenating a minimal H-to-P chain with k cyclic-coordinate steps gives f(r) <= D. These facts alone do not show the limiting value is D.

Here is the full relative version of the source's lem:product-series, obtained by retaining H at the bottom of exactly the same construction. If f(r) <= l for every r, let S_r be the finite nonempty set of length-l chains between H x 0 and P x A_r, allowing repetitions. Projection sends S_(r+1) to S_r. In the compact product of these finite sets, finitely many compatibility conditions are satisfiable by projecting a chain from the largest relevant level. Therefore there is a compatible chain at all levels. No surjectivity of S_(r+1) -> S_r is being assumed.

Inverse limits give a chain of closed groups

    H x 0 = L_0 normal L_1 normal ... normal L_l = P x Z_p^k.

Each factor L_i/L_(i-1) is procyclic. The comparison with the inverse limit of the finite cyclic factors is onto by compactness of compatible representative sets; compatible generators then generate its inverse limit. Put J_i=L_i intersect P and B_i=pr_(Z_p^k)(L_i). There is an exact sequence

    1 -> J_i/J_(i-1) -> L_i/L_(i-1) -> B_i/B_(i-1) -> 1.       (2.1)

For its kernel, cancel an element's projection using an element of L_(i-1); what remains lies in J_i. Every B_i is a closed Z_p-submodule. The rank increments are at most one and sum to k. Exactly k steps therefore have rank increment one. At these steps L_i/L_(i-1) is infinite procyclic, hence Z_p, and its finite subgroup J_i/J_(i-1) is trivial. All other J-factors are finite cyclic. The chain J_0=H to J_l=P consequently has at most l-k nontrivial steps. Hence

    ell(P,H)+k <= l.                                         (2.2)

This proves that f(r) eventually equals D. If it never did, every value would be <=D-1 and (2.2) with l=D-1 would contradict the definition of D. Once it reaches D, monotonicity and the upper bound keep it there. All subgroups, not just normal H, are covered.

This is a direct reuse of the paid source proof, not a proposed new bridge. In particular its relative formulation is not being nominated as a theorem merely because the manuscript states the absolute version.

## 3. A genuinely terminating finite calculation is already available

At any fixed r, finite group operations calculate f(r) exactly. One elementary algorithm has vertices all subgroups S containing H x 0. From S, for each g in its normalizer, add the edge

    S -> <S,g>

when the group grows. Every edge is normal with cyclic quotient, and every normal cyclic extension arises this way. Breadth-first distance to P x A_r is f(r). Exhaustive finite subgroup enumeration, or simply exhaustive subsets of the finite multiplication table, suffices to implement the graph. This has no claimed useful complexity.

The same calculation gives d inside P. Repeating the fixed-r calculation until f(r)=D is therefore an algorithm that is proved to terminate, by Section 2. Equality is a valid stopping condition; a plateau f(r)=f(r+1)<D is not. One can preserve the complete subgroup graph, distances, and a shortest chain as a finite certificate at the stopping level. Thus it would be false to report that no effective algorithm or no finite certificate exists. What remains missing in the intended operation is a structural bound on that stopping level and a controlled reduction of the certificate size. No unbounded execution of this algorithm was run in this session.

For fixed p, |P| and k, a finite maximum over multiplication tables also exists, and exhaustive enumeration combined with the terminating search could compute it. That observation is again paid finite enumeration, not the sought quantitative operation.

## 4. An exact compressed finite subgroup model

The full subgroup graph can be replaced by explicit finite group and abelian-lattice data. Let A be any finite abelian p-group, in particular A_r. For S <= P x A set

    Q = pr_P(S),    B = S intersect A,
    f:Q -> A/B,    f(q)=a+B whenever (q,a) belongs to S.

Then Q <= P, B <= A, and f is a homomorphism. Conversely any such triple gives exactly the subgroup

    S(Q,B,f) = { (q,a): q in Q, a+B=f(q) }.                   (4.1)

The definition of f is independent of the chosen lift because the difference lies in B. Closure in (4.1) follows from the homomorphism identity, and its projection is Q since every coset f(q) has representatives. Thus the parameterization loses no nongraded or diagonal subgroups. It is unique with these conventions. No split extension of S itself is assumed.

Containment S_i <= S_j is equivalent to

    Q_i <= Q_j,  B_i <= B_j,
    f_j|Q_i = reduction_(A/B_i -> A/B_j) f_i.                 (4.2)

Under (4.2), normality S_i normal S_j is equivalent to Q_i normal Q_j and

    f_i(y q y^(-1)) = f_i(q) in A/B_i
        for all y in Q_j, q in Q_i.                          (4.3)

Indeed conjugation by (y,a) sends (q,b) to (y q y^(-1),b), since A is central. Equation (4.3) retains exactly the conjugation information that an unmarked abelian quotient would discard.

The bottom condition H x 0 <= S is H <= Q and f|H=0. Bottom and top triples for the desired chains are (H,0,0) and (P,A,0).

There is also an exact cyclic-edge test. Under (4.2)-(4.3), let C=B_j/B_i. There is a central exact sequence

    1 -> C -> S_j/S_i -> Q_j/Q_i -> 1.                       (4.4)

If Q_j=Q_i, the quotient is C, so cyclicity is simply cyclicity of C. Otherwise Q_j/Q_i must be cyclic, say of order q=p^v, v>=1. Choose x in Q_j mapping to a generator, choose a representing f_j(x), and choose b representing f_i(x^q). By (4.2),

    delta = q a - b mod B_i belongs to C.                    (4.5)

The quotient in (4.4) is generated by the central group C and t=(x,a)S_i, with the one additional relation q t=delta. There are no further relations: its order is q|C| by (4.4), equal to that of the presented central extension. In particular it is abelian. Modulo p its presentation gives

    dim_Fp (S_j/S_i)/p(S_j/S_i)
          = 1 + dim_Fp C/(pC + <delta>).                     (4.6)

A finite abelian p-group is cyclic exactly when its quotient modulo p has dimension at most one. Thus the nontrivial-Q edge is cyclic precisely when

    C = pC + <delta>.                                       (4.7)

Nakayama for a finite abelian p-group also says (4.7) means C=<delta>; the zero group C is allowed. The criterion is independent of lift choices, since a change changes delta by p^v C, which is in pC. Changing the generator x leaves cyclicity invariant because it is the group-theoretic condition (4.4).

For A_r the B_i are submodules of (Z/p^r)^k and can be represented by lattices between p^r Z^k and Z^k. Homomorphism conditions, (4.2), (4.3), and (4.5) are finite congruences after choosing representatives. Smith normal form computes C/pC and tests (4.7). Q_i and their conjugations are evaluated in the fixed multiplication table P. This supplies an exact finite matrix-and-group system for every proposed chain length, with diagonal mixing retained. It is substantially more explicit than treating the finite chain sets S_r as uninterpreted compactness data, but is still elementary finite subgroup algebra; no contribution verdict is asserted.

## 5. Why a local rank-charge argument is insufficient

The inverse-limit proof subtracts k genuinely torsion-free rank-increasing steps. At finite r a cyclic factor can simultaneously absorb a nontrivial P-intersection and a long cyclic coordinate. For example let P=C_p=<x>, A=C_(p^r)=<a>, and

    L_0=1,
    L_1=< (x,a^(p^(r-1))) >,
    L_2=P x A.

Both steps are normal and cyclic: L_1 has order p and the second quotient is C_(p^r), because its relation expresses x as a power of a. At the second step the intersection with P grows from 1 to P while the projection to A grows from its order-p subgroup to all of A. The growth in the A-coordinate is unbounded as r grows. The earlier step had no P-intersection growth; the global chain still has the correct two steps.

Therefore 'a large A-projection increment forces no P-intersection increment at that same step' is false. In the model of Section 4 this failure is exactly the nonzero coupling delta. A successful finite replacement of (2.1) has to rearrange or globally charge the whole chain, retaining (4.3) and (4.7). Simply replacing finite cyclic lengths by Z_p-ranks in each edge loses this extension data. This example is a control on a proposed proof strategy, not a counterexample to the desired structural bound.

## 6. A calculated delay family, extending the primary example

The primary Example 5.15 of Kuhn–Lloyd already shows that product additivity can fail, using P=C_8 semidirect C_2 and H=C_2. Its precise normal chain was read and visually checked. The following parameter calculation makes the delay in Section 2 explicit. It is retained as an elementary diagnostic expansion of that primary construction, not as a substitute nominee.

For every prime p and m>=3 define

    P_(p,m)=<b,c | b^(p^m)=c^p=1,
                       c b c^(-1)=b^(1+p^(m-1))>,
    H=<c>,     A_r=<a> of order p^r.

The indicated automorphism of C_(p^m) has order p: its pth power is 1 modulo p^m, and none of its first p-1 powers is 1. This is a semidirect product of order p^(m+1), with unique coordinates b^i c^j. Its commutator subgroup is <b^(p^(m-1))>. It is central, and c commutes with b^p. The normalizer of H is <b^p,c>. Indeed conjugating c by b^i introduces b to a nonzero multiple of i p^(m-1), so it stays in H exactly when p divides i. H is not normal in P.

The chain

    H normal <b^p,c> normal P

has cyclic factors of orders p^(m-1) and p, and ell(P,H)=2 since H is not normal in P. Thus the stable value for (P x A_r,H x 0) is 3.

For 1<=r<=m-2 put L=<c,a b^p>. The generator a b^p commutes with c, so H normal L and L/H is cyclic. Further,

    (a b^p)^(p^(m-2)) = b^(p^(m-1)),                       (6.1)

because a has order at most p^(m-2). Hence L contains the whole commutator subgroup of P x A_r and is normal. In the quotient, c=1 and a=b^(-p), so the quotient is cyclic, generated by b. We have a length-two chain. Length one is impossible because H remains nonnormal. Thus f(r)=2 in this range.

Conversely suppose H normal L normal P x A_r is a two-step cyclic chain. Since L/H is cyclic, write L=<H,x>. Necessarily x normalizes H, hence x=a^u b^(p v)c^w. Multiplying by c^(-w) makes x=a^u b^(p v) without changing L. The Frattini quotient of P x A_r is C_p^3 on a,b,c: its commutator subgroup is contained in its pth powers. For (P x A_r)/L to be cyclic, L must kill at least two independent directions there. H kills c, and x can add only the a-direction. Therefore u is a unit modulo p.

Normality of L implies b^(p^(m-1)) belongs to L. Since L=<c> x <a^u b^(p v)> and these factors commute, this requires an integer t with

    u t = 0 mod p^r,
    p v t = p^(m-1) mod p^m.                                (6.2)

The first condition gives p^r|t. If r>=m-1, the left side of the second is divisible by p^m, a contradiction. A three-step chain exists by concatenating the two-step chain in P and the A_r coordinate. Consequently

    ell(P_(p,m) x C_(p^r), H x 0)
      = 2 for 1<=r<=m-2,
      = 3 for r>=m-1.                                       (6.3)

The least stabilization precision is exactly m-1. In particular there is no uniform bound depending only on p, k=1 and ell(P,H)=2. There are arbitrarily long proper plateaus of f(r). Bounds allowed to depend on |P| or its exponent are not refuted.

The retained calculation checks the integer congruence compatibility in 160 cases and independently constructs literal multiplication tables for seven groups of orders 32 through 729. It enumerates every cyclic extension of H using its normalizer, tests normality by conjugation, and tests whether the top quotient is cyclic. All seven exact lengths agree with (6.3). These finite calculations support the derivation; the universal proof is the argument above.

## 7. Returning the reduction to the actual chromatic mechanism

The source height-gluing proof starts with a nonzero T(k)-test of U_P(L_T(l)S), uses ring nilpotence to obtain a nonzero K(k)-local commutative algebra B, and uses the HKR full-mark trace to obtain rational nonvanishing for U_(P x A_r)(L_T(l)S) for EVERY r. The trace is

    N_(k,r)=p^(k^2(r-1)) product_(i=0)^(k-1)(p^k-p^i),

not an explicit finite sharpness spectrum. Rational gluing gives ell(P x A_r,1)<=l for every r. Equation (2.2), at H=1, then gives k+ell(P,1)<=l. Our finite-model calculation is compatible with this use: if a structural R were available, the group-theoretic inference could be made at that prescribed R. It does not remove the height-zero case or replace the coherent product comparison by a symmetric equivalence.

For an embedded H, the source's actual support proof uses normal conjugates inside layers, the finite-gluing vanishing, incoming and outgoing orthogonality, and a compact irreducible support. Section 2's relative group calculation does not produce a new right adjoint for nonnormal H, or skip those conjugation terms. Its chromatic consequence is only the already paid equality

    r_n(P x A_r,H x 0)=f(r),    n>=0,

so (6.3) describes losses in a family, not new sharpness spectra. For losses below f(r), source prime separation supplies the existential compact witnesses. It does not give their cellular data.

The strongest primary constructive alternative was also checked: Kuhn–Lloyd's Smith-to-Floyd proof takes an already known rank deficit and applies a p-local symmetric-group idempotent to a smash power. It retains parity, uses the ker(q) filtration at p=2, and uses hook-length p-core idempotents. This cannot create a rank-deficit seed from our finite subgroup graph. Its tensor power is explicit relative to that seed, not uniformly in (P,H,n,r). Applying it to I105's unresolved quantitative realization target would leave that old target unchanged and unpaid; no such retry is offered.

## 8. Strongest endpoint and exact unpaid operation

The integrated construction pays (i) eventual relative product stabilization by the source inverse-limit mechanism, (ii) a terminating finite equality search with an honest stopping condition, (iii) an exact subgroup/normality/cyclic-quotient system reducing a finite chain certificate to homomorphisms and abelian congruences, and (iv) the exact delay calculation (6.3), including a rigorous obstruction to bounds that forget the exponent/order.

What did not close is a structural finite-precision elimination or chain-exchange argument that simultaneously preserves the conjugation equations (4.3) and cyclic-extension condition (4.7), and yields an a priori bound R from the allowed finite structural data for every embedded pair P,H and every k. The source compactness proof and the finite matrix system do not themselves bound that elimination. The diagonal example rules out only a local charging shortcut. The modular examples rule out only a bound using p,d,k alone. Neither is a general impossibility result.

There is no frozen theorem and no author-proof nominee. The direct relative compactness reuse, finite enumeration, and parameter expansion of the primary example are retained as reductions, not submitted for a new verdict. No global exhaustion, literature priority, explicit-spectrum bound, other localization/functor consequence, or acceptance/count is asserted.
