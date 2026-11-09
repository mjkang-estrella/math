# W025: an explicit consumer and the cost it does not remove

Parent derivation, 2026-10-08 local; independent multiplier audit still live.
No numerical run. Verified complete factoring improvement: **NONE**.

Update after the Opus audit: this document's generic exponent frontier is a
sufficient bound, not an optimum for the structured root coefficients.
Known coefficient valuations give stronger precision-truncation options;
see W025-parent-disposition.md. The explicit-anchor consumer and its remaining
M-record cost are unchanged by that correction.

## Group carry searches by the normalized stride

A normalized W025 chart supplies

    E(x,y,tau)=c'*(u+Nv)-sigma*P(x,y)-Q'*tau.

Although c' and the coefficients of P vary with the chart, Q' is an ell-power
between ell and the old Q. There are only O(log Q) possible strides per base.
Thus varying multipliers do NOT prevent the ordinary explicit-anchor carry
consumer from sharing babies. They do prevent silently sharing a kernel whose
nonlinear coefficient array was required to be the same across charts.

For one stride and one dyadic carry-length class, let K be the number of
EXPLICIT point anchors and T their common carry-length upper bound. Check alpha
is a unit. Put beta=alpha^Q'. For an interval starting tau0, split it into
blocks of b carries. At each block create the giant

    g=alpha^(c'*(u+Nv)-sigma*P(x,y)-Q'*tau0),

and test collisions against beta^j, 0<=j<b, using a monic product and ordinary
multipoint evaluation modulo N. The final block uses its actual length;
grouping by its length or binary decomposition avoids unrepresented padding.
No high-order premise is needed for W020's localized annihilator recovery.
Retain sign/point/carry tags, nonzero exponents and the original uniform alpha.

The paid setup and point cost is K. The number of giant records is
O(K+K*T/b), and b babies cost O(b), up to polynomial logarithms for binary
exponents, polynomial arithmetic and localization. Choose a capped integer
b near sqrt(K*T), with direct enumeration if this is outside the useful
range. A valid conservative envelope is

    O~(K + sqrt(K*T)).

If K>=T, simply enumerating every carry for each explicit point is unnecessary:
take b=T, whose O(K+T) cost lies in the displayed envelope. Different prime
bases, strides, length classes and strata cost polynomial logarithmic factors.
This is the established monic collision consumer applied to the NEW public
anchors, not a new multipoint theorem or an implicit evaluation of the anchors.

This finishes one genuine computation after multiplier acquisition. It also
shows its limitation. In the original weighted cover K=O(M), and even an ideal
canonical root has a common width on the scale

    A=sqrt(N)/M^(3/2).

W025 does not improve this width: c'W/Q'=cW/Q and c>=1. With M=N^m,
the resulting explicit-record cost model includes the terms

    N^m and N^(1/4-m/4),

whose best balance is m=1/5. This is a barrier to THIS proved cost envelope,
not a lower bound on algorithms, on all input instances, or on factoring.
The construction can repair inflated carry costs, but beating this envelope
requires computing the joint anchor family without its M explicit records,
or a different cover with a smaller genuine width. An improved interval bound
alone cannot be promoted to that missing computation.

## Anisotropic quartic bookkeeping at M=N^(1/4)

The general fixed-monomial construction gives a useful exact optimization
rule. For weights w_nu on one ordinary box and A=max(1,ceil(W/Q)), minimize
the publicly computable upper envelope

    A * product_(w_nu>T) ceil(w_nu/T) + D*T,

checking B<Q and comparing with the original representation. The number of
weights is fixed. This is acquisition bookkeeping, not a parameter sweep.

For exponent notation only, let w_nu=N^a_nu, A=N^c, T=N^t. The balanced
choice satisfies

    t = c + sum_nu max(a_nu-t,0),

when positive powers dominate constants. The left minus right is strictly
increasing, so sorting the fixed list of a_nu determines the active set and
the candidate t by rational arithmetic. Integer implementations use the
ceiling formula above, not this asymptotic notation.

Take top-stratum U*V~M, W~sqrt(MN), H~M^(2/5), and M=N^(1/4).
Then c=1/8. Order U>=V. If both coordinates vary, put

    a=log_N(U/H), b=log_N(V/H), a+b=1/20, a>=b>=0.

For a<=1/32, every quartic monomial has weight at most A, so T=O(A)
already suffices and no multiplier is needed. For 1/32<a<=1/20, the only
active leading monomial in the exponent model is x^4. Indeed

    t=(1/8+4a)/2=1/16+2a,
    3a+b=1/20+2a < t, and 3a<=t.

A two-variable integer feasibility problem for c_multiplier,k4 therefore
suffices; use K4=ceil(Zx^4/T), B=K4. All other finitely many terms have
weight O(T). Constants/ceilings only change the fixed carry multiplier.

For a signed singleton-v chart, write V=N^v with 0<=v<1/10 and
a=3/20-v. The exponent frontier becomes

    t = 1/16+2a,                 1/20<=a<=1/16;
    t = (1/8+7a)/3,              1/16<a<=3/20.

The latter is W025's two-active-coefficient construction. Its boundary
A<=Zx^2 is exactly a>=1/16. At a=3/20 this recovers t=47/120.
In all these top-stratum regimes B has exponent t-c<=4/15<1/2,
so B<Q is eventually satisfied with room for fixed constants. Finite inputs
still require the explicit check. The complete all-stratum implementation
has not been costed by this top-stratum calculation.

These thin windows are not all disposable small-factor cases. Optimal
weights give p on scale V*sqrt(N/M). At M=N^(1/4), its exponent is
3/8+v, and a square-root small-factor product comparator has exponent
3/16+v/2. It exceeds 1/5 once v>1/40. W025's two-active regime extends
to v<7/80, so a nonempty part survives that simple preprocessing comparison.
This observation makes the representation repair relevant; it does not
remove the explicit-anchor or complete-evaluator cost above.

## Distinct attempts at reducing root-chart acquisition

Projective coordinates expose an exact homogeneity that rectangular charts
ignore. Fix a unit slope a modulo H and write u=a*v+H*x. Acquire
r_a^2=4N*a modulo Q. A degree-d truncated root is rational in v. Multiplying
by v^(d-1) makes it the explicit homogeneous polynomial

    P_a(x,v)=r_a*sum_(i=0)^d binom(1/2,i)*H^i*a^(-i)*x^i*v^(d-i)
             modulo Q,

provided H^(d+1) is divisible by Q. There are only O(H) slope charts,
instead of O(H^2) residue-pair charts. All v are ell-units after stripping
the common valuation. The scaled true sum is v^(d-1)*S.

This is an actual alternative acquisition, but two costs spoil the first
implementation. The transformed ordinary domain is a lattice parallelogram,
not the naive full x,v rectangle. More seriously, the scaled width is at
most V^(d-1)*W. For d=2 in the balanced regime, H~M^(2/3) and
V~sqrt(M), so even BEFORE coefficient-height inflation the common carry
scale becomes sqrt(N)/M. M pairs then give sqrt(N) occurrences, erasing
the original cover's factor M^(1/2) saving. No gain is claimed.

There is a precise way the discarded information could repair that count:
v*S is divisible by v, so the represented tau must satisfy

    P_a(x,v)+Q*tau = 0 modulo v.

Since gcd(Q,v)=1, this is one residue class modulo v and restores the
missing density. It is not free. Its residue uses Q^(-1) modulo a VARIABLE
v, and changes with x. Substitution creates variable carry strides and a
quadratic modular remainder. Explicitly computing this per pair returns to
the M-anchor cost. A computation preserving that congruence jointly with
the projective polynomial would be materially different from dropping it
or repeatedly enlarging the common interval. No such fast consumer has
yet been obtained; do not delegate a purported speedup without one.

The next main task is the joint nonlinear-anchor computation or a different
starting point. Neither the existing W025 audit nor another root-identity
certificate is needed to continue that constructive work.
