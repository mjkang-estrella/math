# W032: retaining a linear trend still bounds uniformly sampled hits

Parent derivation, 2026-10-08. **Accepted at the scoped level** in
[the independent review](W032-near-top-review.md). No experiment.
Verified complete factoring improvement: **NONE**. This is a distinct lower-
order filter; the completed difference audit owns the order 2R+1 note.
This extension's independent audit is complete; its selector qualification
is incorporated below.

The negative high-order result raises a constructive question: keep part of
the polynomial instead of canceling it completely. Use D=4^R(2R+1)!,
s=2R-1, and canonical unit inputs a_i=a0+iD, 0<=i<=s. Define Z_s by the
usual order-s binomial finite difference of d_R(a_i), reduced modulo N.
The interval of possible starts has length L0=N-sD, assumed positive.

As in the accepted floor decomposition, on each such stencil

    d_R(a_i)=J(i)+floor(Q(i)) modN,

where J is the restriction of G_R(a^2) minus a constant and Q has degree
at most 2R-2 in i. The small residue labels may vary WITH a0, but are
constant within each stencil. Since s exceeds deg Q,

    Delta^s floor(Q)=-Delta^s {Q}=c,   |c|<B=2^(s-1)=4^(R-1).

Only the leading a^(2R) term of J survives its s-th difference. All other
powers of a in G_R(a^2) are even and at most 2R-2. Let

    g=product_(j=1..R)(2j-1)^2 / [4^R(2R+1)!],
    A=g*(2R)!*D^(2R-1),
    u=a0+sD/2.

The ordinary identity Delta_h^(d-1) x^d=d!*h^(d-1)*(x+(d-1)h/2)
gives

    Z_s = A*u+c modN,     c integer, |c|<B.             (1)

D is even, so u is an integer. Every factor of the numerator and denominator
of A is below leastprime(N) on the stated branch, so A is a unit modulo N.
Its denominator is interpreted only after the unit check. In fact A is an
integer here because the power of D clears the displayed denominator.
No huge exact A need be formed: compute it modulo N with paid arithmetic.

## A root count that does not assume a random carry

For any prime p dividing N, equation (1) and p>2R+1 imply

    p | Z_s  =>  u=-c*A^(-1) modp for some c in {-B+1,...,B-1}.

Regardless of how c depends on the entire canonical representative, this
is at most min(p,2B-1) residue classes of a0 modulo p. Consequently the
number of VALID unit stencils with p dividing Z_s is at most

    min(L0, (2B-1)*ceil(L0/p)).                        (2)

This upper bound counts all potential starts as a superset, so imposing
the unit-stencil condition cannot invalidate the count. Dividing by L0
is valid for a uniform start in the entire interval, with invalid stencils
retained as a separate branch. It is not the conditional probability after
resampling until every stencil point is a unit.

For distinct primes N=pq, the probability of a proper FILTERED gcd per
fresh uniform start is at most

    min(1,(2B-1)*(1/p+1/q+2/L0)).                      (3)

This is a union bound; both-component zeros give gcd N. Initial gcd exits
are separate. Their total probability is at most

    (s+1)*(1/p+1/q+2/L0),

again by a union bound over the points, whether or not later points would
actually be reached. No independence among carries or points is assumed.

For a comfortable width guard sD<=N/2, L0>=N/2. The same factorial-height
argument as in the higher-order filter gives R=O(logN/loglogN) and
B=N^o(1). On any input family with p<=q and p>=N^epsilon for fixed positive
epsilon, the total success probability of this stated random-start filter,
INCLUDING its initial gcd exits, is at most p^(-1+o(1)). Thus obtaining
constant success from such trials requires p^(1-o(1)) attempts by a union
bound. Each attempt has nonzero cost; this cannot improve on the already
accepted soft sqrt(p) small-factor search in this sampling model.

This conclusion does not assume a lower success probability, and does not
assert a bound for an adaptive nonuniform starting-point algorithm. It also
does not dispose of individual d_R values observed during the filter if
their own gcds are tested as additional outputs: those are extra success
events, with their own still-unproved higher-digit law.

## What was removed and what remains constructive

This lower-order filter retains a genuine degree-one term. Unlike the
order-2R+1 filter, its gcd need not be trivial on large-factor inputs. But
the bounded carry gives an explicit small union of possible prime roots,
which controls UNIFORM starting-point search without guessing its law.

Forcing the linear part to zero modulo N is not a canonical shortcut:
A is a unit, so it would require u=0 modN. The full stencil in [0,N)
puts u strictly between 0 and N. A wrapped stencil changes the small residue
labels and is outside this derivation. Even in an enlarged lift family,
forcing the main term to zero would leave only the small c.

The actual computation costs s+1 digit acquisitions and their finite
difference, conservatively soft O((R+1)^2*poly(logN)). A supplied start can
also be screened by a product over ALL possible arguments A*u+c,
|c|<B, though that different consumer pays its own interval-product and
localization cost and may hit more factors. Compact uncertainty notation
does not evaluate that product for free.

One possible next route is an explicitly priced selector using a proved
useful dependence between c and u. Any changed selector or consumer needs
its own actual-input proper-split guarantee and full cost analysis. The
uniform-start bound supplies neither that guarantee nor a theorem that
such a correlation is the only route. This note resolves the specific
near-top sampler's amplification premise under the explicit width guards.

An additional concrete targeting rule also has a simple limitation. Select
only starts whose centered representative t of A*u modulo N satisfies
|t|<=T. The filtered gcd then equals gcd(t+c,N), with |t+c|<T+B.
If leastprime(N)>T+B, this produces only gcd 1 or N. Selecting a globally
small linear signal is therefore insufficient; useful targeting would
need proximity to an unknown prime multiple without forcing global
smallness. This statement concerns this filter, not initial or individual
digit exits, and does not claim such a selector is impossible.
