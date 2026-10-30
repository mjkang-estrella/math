# T009P102: author proof at the frozen scope

This is an author proof, relative to the stipulated pinned theorem and the classical
primary input specified below. It assigns no independent correctness or contribution
verdict. The frozen statement is SCOPE.md, SHA256
`fc1e349511e87ebd6a0ba0c1533b2c8a81e5fca100e30e9ef2ad7cf5915f002b`.
All primes, including 2, and all finite levels in that statement are retained.

## 1. Inputs and notation

Write C=F^p and V=F^times/C^times additively, with [fg]=[f]+[g].
The elementary p-basis construction is the pinned equal-characteristic source
`02-symbols.tex`, `lem:p-basis`: if [F:C]=p^d is finite, any p-independent
list extends to a p-basis t_1,...,t_d. Its monomials of exponents between 0 and
p-1 form a C-basis, and the commuting Euler derivations D_i satisfy
D_i(t_j)=0 for i!=j and D_i(t_i)=t_i. Thus D_i^p=D_i.
The intersection of all ker D_i is C; the intersection of ker D_i for i>=2
is C(t_1). For an independent pair f,g, C(f) intersect C(g)=C.
These statements also follow directly by comparing the monomial coefficients.

Use the relative differentials Omega=Omega^1_{F/C}. The dt_i, or equivalently
dt_i/t_i, form an F-basis. Indeed every element has a monomial expansion over C,
so these differentials span; evaluation on the D_i proves independence. In
particular dh=0 iff h is in C. The map

    ell: V -> Omega,        ell([h])=dh/h

is well defined, F_p-linear and injective. The alternating pairing

    [u],[v] |-> du/u wedge dv/v

annihilates [x] tensor [1-x] and therefore factors through W=K_2^M(F)/p.
Only this elementary factorization, not injectivity of the degree-two differential
symbol, is used. It works in characteristic 2 as well: the exterior square is
alternating in every characteristic.

The only nonelementary classical theorem used in passing between levels is:

(P) K_2^M(F) has no p-torsion when char F=p.

This is the degree-two case of Geisser--Levine, *The K-theory of fields in
characteristic p*, published version, Theorem 8.1, pp.489--490. The theorem
and its proof were read directly. It reproves Izhboldin's theorem; Izhboldin's
2000 author survey, Section 2.4, Theorem 6, also records it (and credits the
n<=2 case to Suslin). The full earlier proof dependency chain in motivic
cohomology is not reproduced here. This is a cited theorem, not an additional
unproved bridge about the proposed reconstruction statement.

The n=1 reconstruction input is the pinned equal-characteristic `thm:main`
in `01-introduction.tex`, proved in `02-symbols.tex` through `05-fields.tex`.
It reconstructs the actual fields and named algebraically closed bases from
V_1 and R_1, up to one F_p unit. All five proof sections were read directly.
The mod-ell and pro-ell companions have char F!=ell at their top fields;
their Kummer/perfection operations are not substituted into char F=p here.

## 2. A classical logarithmic-derivative identity

Lemma 2.1. Let D be a derivation of a field F of characteristic p, with
D^p=D. If u is nonzero and A=D(u)/u, then

    D^(p-1)(A)+A^p=A.                                      (2.1)

Proof. Write M_b for multiplication by b. The classical operator formula is

    (D+M_b)^p=D^p+M_(D^(p-1)b+b^p).                        (2.2)

For completeness, define B_0=1 and B_(j+1)=D(B_j)+b B_j.
The product rule and induction give

    (D+M_b)^m = sum_(j=0)^m binom(m,j) M_(B_j) D^(m-j).

Also, by the same recurrence, B_m is the sum over set partitions of
{1,...,m}, with each block of size s contributing D^(s-1)b.
For m=p, the coefficient of a monomial with m_s blocks of size s is

    p! / product_s( m_s! (s!)^(m_s) ),   sum_s s m_s=p.

Except for the single block of size p and the p singleton blocks, every
factor in the denominator is prime to p, so this integer coefficient is
divisible by p. Thus B_p=D^(p-1)b+b^p. The intermediate binomial
coefficients in the operator formula also vanish, proving (2.2).
This is Jacobson's classical calculation, *Abstract derivation and Lie
algebras* (1937), Section III.12, equations (28)--(33), Theorem 15,
pp.223--224; the formula and proof were read and visually checked.

Now M_u^(-1) D M_u = D+M_A. Its p-th power is itself, because D^p=D.
Apply (2.2) and cancel D to obtain (2.1). QED.

Lemma 2.2. Suppose in addition D(r)=0 and r^p!=r. If A=D(u)/u and
rA=D(v)/v for nonzero u,v, then A=0.

Proof. Apply (2.1) to A and to rA. Since D(r)=0, the latter identity minus
r times the former is (r^p-r)A^p=0. A field has no zero divisors, so A=0. QED.

Lemma 2.2 is a direct corollary of the classical identity. No novelty is
claimed for this identity or the corollary in isolation.

## 3. Infinitesimal Steinberg rigidity (Proposition I)

Assume the hypotheses of Proposition I. For f in F^times write

    eta(f)=ell(delta([f])).

Then eta(fg)=eta(f)+eta(g), eta(h)=0 for h in C^times, and each eta(f)
is the logarithmic differential of some nonzero element of F. Applying
the exterior differential symbol to the assumed relation gives

    eta(x) wedge d(1-x)/(1-x) + dx/x wedge eta(1-x)=0.       (3.1)

Fix f not in C. In particular f!=0,-1. Since -1 is a p-th power,
delta([-f])=delta([f]). Substitute x=-f into (3.1) to obtain

    df wedge ( eta(f+1)/f - eta(f)/(f+1) )=0.

As df!=0 and Omega is an F-vector space, there is some b in F such that

    eta(f+1) = r eta(f)+b df,       r=f/(f+1).               (3.2)

Extend f to a p-basis t_1=f,t_2,...,t_d, where d>=2. For each i>=2,
D_i(f)=0 and hence D_i(r)=0. Choose nonzero u,v representing delta([f])
and delta([f+1]). Evaluation of (3.2) on D_i says

    D_i(v)/v = r D_i(u)/u.

Moreover r^p!=r. Otherwise r belongs to F_p, since T^p-T has exactly
its p roots in F_p in every characteristic-p field. Solving
r=f/(f+1) would put f in F_p (the value r=1 is impossible), contrary
to f not in C. Lemma 2.2 therefore gives D_i(u)=0 for every i>=2.
The p-basis monomial calculation implies

    u in C(f)^times.

Consequently there is a scalar lambda_f in C(f) with

    eta(f)=lambda_f df/f.                                 (3.3)

More explicitly lambda_f=D_1(u)/u, which belongs to C(f).
This step removes all transverse components of an arbitrary delta; it
makes no assumption that delta is itself compatible or invertible.

Now take p-independent f,g. Their logarithmic differentials are F-linearly
independent, and fg is not in C. Using multiplicativity of eta and (3.3),

    lambda_(fg)(df/f+dg/g)=lambda_f df/f+lambda_g dg/g.

Independence gives lambda_f=lambda_g=lambda_(fg). Every f outside C has
a neighbor g outside C(f). Furthermore, if f,g are p-dependent then
C(f)=C(g), and any h outside that degree-p subfield is p-independent
from both. Hence the graph of p-independent pairs on F minus C is
connected. It follows that lambda_f is a single element lambda of F.
Choosing one independent pair shows

    lambda in C(f) intersect C(g)=C.

Fix f outside C and use its Euler derivation D_1 as above. We have
D_1(u)/u=lambda and D_1(lambda)=0. Equation (2.1) gives lambda^p=lambda,
so lambda=c for some c in F_p. Thus eta(f)=c df/f for all f outside C;
the same identity holds for f in C^times since both sides are zero.
Injectivity of ell gives delta([f])=c[f] for every f, proving the claim.
Uniqueness follows from V!=0. Conversely c id satisfies the assumed
identity since its value is 2c times a Steinberg symbol, which is zero.
This includes p=2 without any division by 2. QED.

## 4. The exact coefficient-level reduction

Lemma 4.1. If an abelian group G has no p-torsion, multiplication by
p^(n-1), for n>=2, induces an injection

    j_n: G/pG -> G/p^n G

whose image is p^(n-1)(G/p^n G), the kernel of reduction to G/p^(n-1)G.

Proof. Only injectivity needs checking. If p^(n-1)g=p^n h, then
p^(n-1)(g-ph)=0. Repeated injectivity of multiplication by p gives
g=ph. The image and kernel assertions follow directly from the quotient
maps. QED.

Apply this to G=F^times (written additively), where absence of p-torsion
is injectivity of Frobenius, and to G=K_2^M(F), using (P).
We distinguish these injections as j_n^1 and j_n^2 when needed.

Reduction V_n(F)/p^(n-1)V_n(F)=V_(n-1)(F) is canonical, as is
V_n(F)/pV_n(F)=V_1(F). Reducing the defining generators of R_n gives
exactly R_(n-1); likewise reduction all the way to p gives R_1.
Tensor base change therefore shows that a compatible isomorphism at
level n induces compatible isomorphisms at all smaller levels. This
argument uses equality of relation submodules and the inverse of the
isomorphism, not merely a one-sided symbol implication.

Lemma 4.2. Suppose n>=2 and Psi is a compatible automorphism of V_n(F)
which reduces to the identity on V_(n-1)(F). There is a unique F_p-linear
map delta: V_1(F)->V_1(F) with

    Psi(v)=v+j_n^1(delta(v mod p)).                        (4.1)

It satisfies the hypothesis of Proposition I.

Proof. Psi-id takes values in the image of j_n^1. Inverting that
injection gives an additive map V_n->V_1. It kills pV_n, because its
image has exponent p and Psi-id is additive. Hence it descends uniquely
to delta on V_1, proving (4.1).

For x!=0,1 choose nonzero u,v with [u]_1=delta([x]_1) and
[v]_1=delta([1-x]_1). Equation (4.1) and compatibility imply, in W_n,

    0 = {x u^(p^(n-1)), (1-x) v^(p^(n-1))}
      = {x,1-x}
        + p^(n-1) ( {u,1-x}+{x,v} )
        + p^(2n-2) {u,v}.

The first term is the exact Steinberg relation. The last term vanishes
modulo p^n since 2n-2>=n, including n=2. Thus j_n^2 of the class
{u,1-x}+{x,v} in W_1 is zero. Injectivity of j_n^2 gives precisely

    delta([x]_1) dot [1-x]_1 + [x]_1 dot delta([1-x]_1)=0.

Changes of u,v by p-th powers do not affect this equation. QED.

When p^2<=[F:F^p]<infinity, Proposition I and (4.1) now give

    Psi=(1+p^(n-1)c) id    for a unique c in F_p.           (4.2)

## 5. Proof of Theorem T at every frozen level

The case n=1 is the stipulated pinned `thm:main`. Its scalar action is
free because V_1(K)!=0, so its orbit statement gives a unique pair
(a,alpha) as in Theorem T. The source's `lem:p-degree` gives
[K:K^p]=p^d with finite d>=2; similarly for L. Thus Proposition I is
available at every later step, with no new hypothesis on K or L.

Proceed by induction on n>=2. Given Theta at level n, its reduction
at n-1 has, by induction, a unique expression a_(n-1) alpha_*, with
alpha:K->L carrying k onto l. Choose any unit a_tilde in A_n lifting
a_(n-1), and let alpha_n be the map induced by alpha at level n.
Both alpha_n and multiplication by a_tilde are compatible isomorphisms:
they carry the defining relation submodule onto itself/the corresponding
submodule, and a unit scales its tensors by its square. Define

    Psi=(a_tilde alpha_n)^(-1) Theta : V_n(K)->V_n(K).

It reduces to the identity at level n-1. Lemma 4.2 and Proposition I
show that Psi=(1+p^(n-1)c)id for c in F_p. Therefore

    Theta=a alpha_n,        a=a_tilde(1+p^(n-1)c) in A_n^times.

This proves existence for all n. The result is independent of the
chosen lift a_tilde by the uniqueness argument next.

Suppose a alpha_n=b beta_n. Reducing modulo p and using the pinned
bijection modulo scalars gives alpha=beta as actual field maps, with
alpha(k)=beta(k)=l. To prove a=b, choose f not in K^p. Its class in
V_n(K) has exact order p^n: if p^(n-1)[f]_n=0, there is a g in K^times
with f^(p^(n-1))=g^(p^n); injectivity of Frobenius forces f=g^p, a
contradiction. Since all orders divide p^n, the order is exactly p^n.
Now (a-b)[f]_n=0 implies a=b in A_n. This also proves uniqueness at n=1.

Conversely a field isomorphism respecting the bases sends every
Steinberg generator to a Steinberg generator, as does its inverse.
A unit scales the tensor square by its square, so every claimed pair
is compatible. The induced degree-two map is a^2 times alpha on
K_2^M/p^n; it is unique because symbols generate W_n. This proves the
bijection and all quantifiers of Theorem T. QED.

## 6. Boundaries of the proof

The reconstruction theorem is for isomorphisms, not noninjective Hom
maps. It assumes the same characteristic p and gives the actual field,
not its perfection. Frobenius F->F itself is not an isomorphism here;
no Frobenius quotient is added. A single finite level is sufficient;
no coherent tower or integral lift is required of the input. No
algorithmic or quantitative reconstruction bound is asserted.

No numerical computation is used as evidence for Proposition I or
Theorem T. The proof of Proposition I uses only finite p-rank>=2 and
is separate from the deeper pinned n=1 reconstruction theorem. The
p-torsion-freeness theorem is essential to the stated lifting argument;
without it, the expansion would yield only a torsion-obstructed
linearized condition. No author gap remains identified at the frozen
scope, but independent adversarial correctness and contribution review
have not occurred.
