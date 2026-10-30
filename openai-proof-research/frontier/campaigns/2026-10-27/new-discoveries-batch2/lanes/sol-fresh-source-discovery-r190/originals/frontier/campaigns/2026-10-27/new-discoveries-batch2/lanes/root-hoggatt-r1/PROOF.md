# Candidate: strict interlacing of q-Hoggatt sums

**Research proof, not accepted or counted.** Main source: Fang–Zhang–Zhao,
arXiv:2505.05873, Conjecture 4.1. Formalization and independent review remain.
This proof does NOT settle BBK Conjecture 5.1.

## Statement and normalization

For a real q>1 and integers m>=1, N>=m-1, define

    F[N,m](t) = sum_{k=0}^{N-m+1}
      q^{m*k*(k+1)/2} prod_{j=0}^{m-1} [N choose k+j]_q t^k.

The Gaussian coefficient is the usual positive real Gaussian coefficient,
with value zero outside 0<=k<=N. All displayed coefficients of F are positive.

**Theorem.** For every q>1 and integer m>=2, the polynomials F[N,m],
N=m-1,m,..., have only simple negative zeros, and consecutive polynomials
strictly interlace. Moreover, if r_1<...<r_d<0 are the roots of a nonconstant
F[N,m], then r_i/q < r_{i+1} for 1<=i<d.

The source's polynomials satisfy

    H[n]^[m](q,t) = F[n+m-2,m](t) /
                   prod_{j=1}^{m-1} [n+m-2 choose j]_q.              (1)

Indeed, MacMahon's boxed-plane-partition product, for k+l=n-1, is

    sum_{pi in PP[k,l,m]} q^{|pi|}
       = prod_{i=1}^k prod_{j=1}^m (1-q^{l+i+j-1})/(1-q^{i+j-1})
       = prod_{j=0}^{m-1} [k+l+m-1 choose k+j]_q /
                         prod_{j=1}^{m-1} [k+l+m-1 choose j]_q.

The latter equality follows by expanding each Gaussian as a quotient of
q-factorials; no extra power of q occurs. Multiply by the source's
q^{m*binom(k+1,2)} and sum over k. The denominator of (1) is strictly positive
and independent of t, so it changes neither zeros nor interlacing.
For q=1, strict interlacing for every m>=2 is the source's Theorem 1.2.
Thus the theorem resolves the exact integer-q, m=2,3 Conjecture 4.1, if the
proof and novelty survive review. The q>1 and all-m extension is one family,
not extra outcomes.

## Classical input: Garloff–Wagner

Write p star h for coefficientwise Hadamard multiplication. Use the following
parts of Garloff–Wagner, *Hadamard Products of Stable Polynomials Are Stable*,
JMAA 202 (1996), 797–809, Theorem 4 (also stated precisely as FZZ Theorem 2.1).
All polynomials have positive leading coefficient and only nonpositive zeros.

1. A nonzero Hadamard product has only nonpositive zeros; its nonzero zeros
   are simple.
2. If g precedes f and b precedes a in weak interlacing/alternation-left order,
   then g star b precedes f star a.
3. For nonzero inputs, the two products have no common nonzero zero unless
   both pairs are proportional, or both pairs are related by multiplication
   by a positive constant times t.

Here 'g precedes f' means either degree(g)=degree(f)-1 and the zeros of g
interlace those of f, or equal degree with the zeros of g alternating to the
left of those of f. This convention is the one used in FZZ.

Two immediate consequences (credited to this classical input, not new claims):

(A) If two pairs have adjacent degrees, positive coefficients, only negative
zeros, and weak interlacing, then their Hadamard products strictly interlace.
The exceptional proportional cases cannot hold: degrees differ and the
constant coefficients are nonzero.

(B) Suppose P has positive coefficients, degree at least one, only negative
zeros, and weak q-separation r_i/q<=r_{i+1}. Suppose R is nonconstant with
positive coefficients and only negative zeros. Then P star R is strictly
q-separated. To see this, P(t) precedes P(qt), while R precedes itself.
Apply parts 2 and 3 to get

    (P star R)(t) strictly alternates left of (P star R)(qt).

The exceptional proportional case is absent because P(qt) is not proportional
to P(t) (constant and leading coefficients, q>1), and the t-multiple case
is absent because all constants are nonzero. The products have equal degree
min(deg P,deg R), have negative zeros by part 1 and their positive constants,
and no common zero. If their roots are s_1<...<s_e<0, this strict alternation
reads s_1<s_1/q<s_2<s_2/q<...<s_e<s_e/q, exactly strict q-separation.
For constant R the output is a positive constant; no separation condition
is needed.

## q-Rolle and q-Markov lemmas, with proofs

Set D_q f(t)=(f(qt)-f(t))/((q-1)t), understood polynomially at t=0.
Its leading coefficient is [d]_q times that of f, and its degree is d-1
when f has positive degree d.

**Lemma 1 (strict q-Rolle).** If f has positive leading coefficient and simple
negative roots r_1<...<r_d with r_i/q<r_{i+1}, then D_q f has exactly one
simple zero y_i in (r_i/q,r_{i+1}) for each i=1,...,d-1, and these zeros
are strictly q-separated.

Proof. At a_i=r_i/q, f(qa_i)=0 and a_i lies in (r_i,r_{i+1}), so the sign
of D_q f(a_i)=-f(a_i)/((q-1)a_i) is the sign of f(a_i), namely (-1)^{d-i}.
At b_i=r_{i+1}, f(b_i)=0 and qb_i lies in (r_i,r_{i+1}), so the sign of
D_q f(b_i)=f(qb_i)/((q-1)b_i) is (-1)^{d-i+1}. Both endpoint values are
nonzero. The intermediate value theorem gives a zero in each disjoint
interval. Since deg(D_q f)=d-1, these are all the zeros and each is simple.
Finally y_i<r_{i+1}, hence y_i/q<r_{i+1}/q<y_{i+1}. QED.

**Lemma 2 (q-Markov on separated roots).** Let f satisfy Lemma 1, with d>=2.
If g has positive leading coefficient, degree d-1, and weakly interlaces f,
then D_q g strictly interlaces D_q f (the constant-versus-linear case has
the usual vacuous root inequalities).

Proof. Since f is squarefree, partial fractions give

    g(t)/f(t) = sum_{j=1}^d c_j/(t-r_j),
    c_j = g(r_j)/f'(r_j) >= 0.

The residue inequalities follow from interlacing: at a nonshared r_j, both
g(r_j) and f'(r_j) have sign (-1)^{d-j}; at a shared root the residue is 0.
Moreover sum c_j=lc(g)/lc(f)>0 by comparing the expansions at infinity.
At a zero y_i of D_q f, Lemma 1 puts both y_i and qy_i in (r_i,r_{i+1}).
Thus (y_i-r_j)(qy_i-r_j)>0 for every j. Using f(qy_i)=f(y_i) gives

    D_q g(y_i)
       = - f(y_i) sum_j c_j/((qy_i-r_j)(y_i-r_j)).                  (2)

The sum is strictly positive. The signs of f(y_i), and hence those of
D_q g(y_i), alternate, with the final sign D_q g(y_{d-1}) positive.
There is a zero of D_q g in every interval (y_i,y_{i+1}). Degree d-2
implies these are all its zeros, simple; strict interlacing follows. QED.

No claim of novelty is made for these general q-difference lemmas. The proofs
are included to remove dependence on possibly mismatched q conventions.

## The coefficient identity

For m>=2 and N>=m, set

    G[N,m] = F[N,1] star F[N-1,m-1].

Then

    D_q G[N,m](t) = [N]_q q^m F[N-1,m](q^m t).                    (3)

Verification: coefficient t^k on the left is

    [k+1]_q q^{m*(k+1)*(k+2)/2}
      [N choose k+1]_q prod_{j=0}^{m-2}[N-1 choose k+1+j]_q.

Use [k+1]_q [N choose k+1]_q=[N]_q [N-1 choose k]_q and
(k+1)(k+2)/2=k(k+1)/2+k+1. The result is precisely coefficient t^k
on the right. The ranges agree, 0<=k<=N-m. All quantities are defined at
the boundary N=m, where both sides are positive constants.

## Induction on m

For m=1, the finite q-binomial theorem gives

    F[N,1](t) = prod_{j=1}^N (1+q^j t).

These polynomials have negative roots, are weakly q-separated, and consecutive
members weakly interlace (the smaller divides the larger).

Assume the required negative-rootedness and adjacent interlacing for level
m-1; for m-1=1 use the weak base statements. For every N>=m, the two factors
of G[N,m] have positive coefficients and only negative roots. Consequence B
of Garloff–Wagner, using the first factor F[N,1], gives strict q-separation
of G[N,m]. Both factors are nonconstant here, since N-m+1>=1.
Also the pairs

    F[N,1], F[N+1,1]
    F[N-1,m-1], F[N,m-1]

have adjacent degrees and weak interlacing. Consequence A gives

    G[N,m] strictly interlaces G[N+1,m].

Lemma 2 then gives strict interlacing of their q-derivatives. Identity (3),
and its version with N+1, turn this into strict interlacing of
F[N-1,m](q^m t) and F[N,m](q^m t). Their common positive argument scaling
q^m can be removed. These pairs cover every N>=m, including the first
positive-constant/linear pair. Lemma 1 and (3) likewise prove negative simple
roots and strict q-separation for every nonconstant F[N-1,m]; increasing N
covers the whole family. F[m-1,m] is a positive constant directly.
This completes the induction and the theorem.

## Scope and strongest objection

The argument is mathematically complete conditional only on the stated
classical Garloff–Wagner theorem and the standard finite q-binomial/MacMahon
identities. Those are dependencies, not unproved new conjectures.

The central eligibility objection is **routine adaptation/subsumption**:
FZZ already gives the same induction at q=1 with ordinary derivatives. The
present argument replaces it by q-differentiation and supplies the required
strict separation invariant. Before credit, an independent reviewer must
decide whether this is a substantive previously unresolved result or a routine
corollary of existing q-separation theorems, and inspect all nearby primary
sources. A complete Lean endpoint is NOT supplied by this research proof.

## References and verification note

- Fang–Zhang–Zhao: https://arxiv.org/html/2505.05873, Conjecture4.1,
  Theorems1.2/2.1/2.2. The normalized induction at q=1 is theirs.
- Garloff–Wagner: https://doi.org/10.1006/jmaa.1996.0348, Theorem4.
  Original author-hosted PDF URL and access limitation are in provenance.json.
- Lamprecht: https://arxiv.org/html/1210.1102, Theorem25, supplies classical
  q-Rolle context; Theorems29/30 are nearby weighted-convolution results.
  Lemmas1/2 above are proved directly, not asserted as novel general theorems.

The derivative substitution alone would be invalid: D_2 applied to
(t+9)(t+10)(t+11) gives 7t^2+90t+299, of discriminant -272. This is why
q-separation is an actual invariant needed by the proof.

The exact coefficient tests and elementary Lean bridge are documented in
discovery.md. They do not constitute a Lean certificate of this theorem.
