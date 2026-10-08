# H017: a valid padded lattice, but an insufficient certified box size

2026-10-08. Native Sol /root/h010_early_dependencies proposed the module;
root checked the determinant and derived a finite-t bound; separate native
Astra /root/h007_additive_relations checked the construction and LLL constants.
Paper analysis only, no lattice reduction, timing, Lean theorem or new attack.
Verified improvement NONE. This is a failure of a specified sufficient
certificate to establish an attractive parameter range, NOT a lower bound on
short vectors, all lattice methods, or coordinate-aware ECDLP algorithms.

## Valid module

Fix m>=2, prime p, and integer polynomial f(x1,...,xm) representing the
specialized summation polynomial S_(m+1)(x1,...,xm,r) modulo p. Each variable's
degree is at most delta=2^(m−1). Choose an admissible monomial order, actual
leading exponent alpha, and normalize its nonzero scalar coefficient modulo p;
take integer coefficient representatives with that leading coefficient literally1.
Vanishing specializations or changed leading terms must be handled explicitly.

The summation-polynomial degree statement and its algebraic-closure root
meaning are in Semaev's [§2, pp.2–3](https://arxiv.org/pdf/1504.01175).
Neither a modular polynomial root nor a tuple of abscissas alone proves a
useful rational-point relation; reconstruction, signs and verification are paid.
Root opened this primary source; the older2004/031 PDF returned403.

Let A={0,...,delta}^m, padding the actual support. For lattice power t>=1 set

    J_l=(t−l)A+l*alpha,  0<=l<=t.

These are nested subsets of tA. For every u in tA, let l(u) be the greatest l
with u in J_l. Use the row polynomial

    x^(u−l(u)*alpha) * f^l(u) * p^(t−l(u)).

All exponents are nonnegative, supports lie inside tA, and every row vanishes
modulo p^t at a root of f modulo p. Scale x_i by positive integer B. Rows have
distinct leading monomials x^u, so their square coefficient matrix is triangular
in the chosen order. This uses a scalar multivariate leading coefficient;
it does not falsely treat a polynomial coefficient in another variable as1.

With D=(delta*t+1)^m and S=sum_(s=0)^(t−1)(delta*s+1)^m, the determinant is exactly

    det(L)=p^(t*D−S) * B^(m*delta*t*D/2).

Indeed sum_u l(u)=sum_(l=1)^t |J_l|=S; summing all exponent coordinates over
the cube gives m*delta*t*D/2. There is no missing monomial from this padded basis.

## What the sufficient certificate actually says

For a row combination h, integer vanishing requires a checked scaled norm
||h(Bx)||_2 < p^t/sqrt(D), in addition to modular vanishing and |x_i|<B.
The standard LLL first-vector upper bound certifies this if

    2^((D−1)/4) * sqrt(D) * p^(t−S/D) * B^(m*delta*t/2) < p^t.

This is only a guarantee for one vector, not enough independent polynomials
or a zero-dimensional extraction ideal. The additional assumption in the
CRYPTO2025 source remains; see H017-small-root-source-gate.md.
Writing b=log_p(B), even discarding the unfavorable LLL factor requires

    b < 2*S/(m*delta*t*D).

The asymptotic right side tends to2/[delta*m*(m+1)] as t grows. Finite LLL
factors require an appropriate p,t regime and cannot simply be dropped when
claiming an executable finite bound.

Root's stronger finite-t screen uses delta>=2 and convexity of x^m on x>=0:

    S = delta^m * sum_(s=0)^(t−1)(s+1/delta)^m
      <= delta^m * sum_(s=0)^(t−1)(s+1/2)^m
      <= delta^m * integral_0^t x^m dx
       = delta^m*t^(m+1)/(m+1).

Consequently S/(tD) <= (delta*t/(delta*t+1))^m/(m+1)<1/(m+1).
Thus the determinant criterion cannot certify b>=2/[delta*m*(m+1)] at ANY
finite t. A large determinant does not prove the absence of useful short
vectors, and this inequality is not such a claim.

## Conditional complete-work comparison

For an ordinary prime-order family with q comparable to p, suppose a factor
base of size Theta(B), fixed m, useful relation probability on the scale
min(1,B^m/p), polynomial-in-log(p) COMPLETE extraction per query, enough useful
independent rows, and a B² sparse linear-algebra ledger. These are assumptions,
not established facts. The resulting optimistic total exponent is

    max(b, 1−(m−1)b, 2b),

with setup, failed queries, signs, verification and rank losses still to charge.
To beat1/2 in this model requires b>1/[2(m−1)] and b<1/4; m<=3 has no such
interval. For m>=4 the padded certificate threshold is already below the first
requirement. At m=4 it is1/80, versus the necessary b>1/6 in that conditional
ledger (the formal balance b=1/5 would give exponent2/5 if extraction existed).

Thus this padded schedule plus this sufficient analysis does not certify the
missing fast relation collector. Its validity repairs the earlier malformed
H015 module, but does not make that collector plausible enough to implement.
Other supports, shifts, systems, heuristic short-vector behavior, useful-rank
analysis or actual cheaper extraction remain distinct possibilities. No general
infrastructure or numerical run is justified by this negative screen alone.

## Symmetric-variable compression: same finite-t certificate ceiling

Sol's final proposal also replaces x_i by elementary symmetric variables e_i.
This representation is established prior art, already recorded in H007; the
new check here concerns this particular padded lattice and weighted norm gate.
A NEW separate Astra review verified the degree, determinant and a stronger
finite-t bound; root checked its proof. No source theorem about automatic root
extraction is being inferred.

A symmetric polynomial with degree at most delta in each x_i is a polynomial
in e_1,...,e_m of ORDINARY total e-degree at most delta. For clarity, lex-leading
partition exponents alpha_1>=...>=alpha_m are eliminated by
e_1^(alpha_1−alpha_2)...e_m^alpha_m. The total number of e factors is alpha_1
<=delta. Such subtraction preserves the individual x-degree bound, and repeating
this leading-term elimination proves the statement without division. It is not
the assertion that every e_i has the same root bound: in fact

    |e_i| <= binomial(m,i)*B^i.

Pad the e-support by the integer simplex A={v>=0:sum(v_i)<=delta}, normalize
the actual scalar leading coefficient, and use the same deepest-level rows.
Then, writing C=product_(i=1)^m binomial(m,i),

    D=binomial(delta*t+m,m),
    S=sum_(s=0)^(t−1) binomial(delta*s+m,m),
    det(L)=p^(tD−S) * B^(m*delta*t*D/2) * C^(delta*t*D/(m+1)).

Each coordinate sum over the simplex equals delta*t*D/(m+1); weighting the
i-th coordinate by i gives the displayed B exponent. The constants C and
the finite LLL factor make the sufficient norm criterion stricter. Dimension
is lower than the cube's, but setting all e bounds to B would be incorrect.

The reviewer's separate finite-t proof is exact:

    S/(tD)=(1/t)*sum_(s=0)^(t−1)
                  product_(j=1)^m (delta*s+j)/(delta*t+j).

For s<t each factor strictly decreases with delta, since its derivative is
j*(s−t)/(delta*t+j)^2. At delta=1 the hockey-stick binomial identity gives
S=binomial(t+m,m+1), hence S/(tD)=1/(m+1). Thus for delta>1 the ratio is
STRICTLY smaller than1/(m+1), at every finite t. Even discarding C and LLL
losses, det(L)<p^(tD) requires b<2/[m*delta*(m+1)], just as above. This is a
simplex-specific proof, not an unsupported transfer of the cube midpoint bound.

So this representation change does not repair the certified collector exponent.
It may reduce matrix size; that is a potential implementation saving only if
there is already a successful complete extraction method. Sol additionally
requires checking integer-zero norm certificates, zero-dimensional output,
finite extraction and reconstruction of the integer polynomial with roots x_i,
box filtering, rational subgroup lifting, signs and final group equations.
Duplicate permutations do not supply useful relation rank. None of these paid
steps is supplied for the favorable box by the determinant analysis alone.

Asymptotic limits also retain their order: with m,delta fixed, choose a large
fixed t and then grow p, or grow t slowly with t^(m−1)=o(log p), to suppress the
LLL penalty in an exponent comparison. Taking t to infinity at fixed p does
not do so. Distinct shifts of individual x coordinates can destroy the
symmetry and require a new argument; the present construction uses the stated
symmetric specialization.

Validation: proposer, root and separate reviewer checked the displayed
finite-t inequalities on paper. `./scripts/check.sh >
/tmp/ecdlp-h017-operator-check.log 2>&1` exited0 from dlp-research, all363 existing
dependency audits passing. No new theorem was added to Lean/Audit.lean; the
paper derivation remains distinct from those compiled checks.
After the symmetric extension, the same check redirected to
`/tmp/ecdlp-h017-symmetric-check.log` also exited0 with363 existing audits passing.
