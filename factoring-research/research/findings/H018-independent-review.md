# H018 — Independent review of the fixed-dimension model

Date: 2026-10-08. Mathematical review of the complete
[parent report](H018-degree-envelope.md) and [original question](../hypotheses/H018.md).

**Disposition: accept the fixed-r enumeration construction, population upper
bound, exact relaxed infimum, dimension comparison, and linear inequality
witness. Revise two local statements: an arithmetic equivalence in the 1.90
comparison and the distinction between floored and unfloored real sublevels.**
Neither correction changes the optimization or its conditional consequences.
The proposed stronger lattice count remains unproved. No achieved useful
population or improved factoring bound follows.

**Verified full factoring complexity improvement: NONE.** This is reviewed
informal mathematics, not an implementation validation, Lean refinement,
smoothness theorem, or novelty claim.

Read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md and research/STATE.md; H018's question and full report;
W001-relations.md Card C and shared accounting; H013-disposition.md; and the
full H014 construction and independent review. H014's accepted mathematical
root-isolation construction is the starting point, not an assumed supply
theorem. STATE's older pending-review description does not supersede that
completed review. H016's processing work and H017's quadratic supply work are
neither assumed nor duplicated.

The claim decisions are:

1. **ACCEPT — domain, labels and degree.** For each fixed integer r>=2,
   k=r-1, monic nonnegative integer f of degree d>k, N>1 and integer H>=1,
   the coefficient lines give a bijective enumeration of the specified
   positive-leading coefficient box. Every line polynomial has degree d.
   This does not extend to signed f with f(1)=0, unchecked nonmonic inputs,
   or r growing with the input.
2. **ACCEPT — norm bound, exact cutoff and polynomial bit work.** The integral
   C0 is valid. Fixed rational eta permits exact powers and integer roots.
   The accepted H014 sublevel method extends to
   O_r((H^(r-1)+S_all) poly(n)) under the stated degree/width promises.
   No particular H018 implementation or explicit uniform exponent in r is
   certified here.
3. **ACCEPT — root-union population upper bound.** Its leading exponent is
   max(ra-Q/delta²,(r-1)a). No lower supply, primitive density or independence
   follows from it.
4. **ACCEPT — exact infimum of the displayed relaxation.** Both branches,
   their comparison, attainment and strict-collection perturbation check.
   The proof does not replace an output upper bound by a necessary cost.
5. **ACCEPT — dimension comparison within that model.** For each fixed eta,
   r=2 minimizes its infimum; r>=6 already exceeds the quoted comparison
   constant at eta=0. This does not rank actual useful yields by dimension.
6. **ACCEPT, with arithmetic wording revision — the linear witness.** The
   fractions s=93/49, u_required=15101/7980 and their gap are correct, as is
   the conditional envelope 19/10. The numerator in the claimed equivalent
   square-root comparison must be 93193, not 93203.
7. **ACCEPT — exact linear construction.** The 3H labels, clipping interval,
   resultant expansion, sign, cutoff and primitive normalization are valid.
   Zero norms are separate cases, and field suitability remains an obligation.
8. **REVISE the literal real-set wording; ACCEPT the conditional calculation.**
   The dilation identity is for the unfloored real cutoff. Its integer points
   agree with the floored acceptance rule. Assuming the proposed uniform
   lattice count, the unchanged model forces c³>=64/9. This does not prove
   that count, its applicability, or an obstruction under a different norm law.
9. **REJECT any stronger promotion.** Neither relaxed attainment, the 1.90
   witness nor homogeneity establishes useful supply, smoothness, paid ideal
   processing, rank, square roots, proper splitting or a new complexity bound.

The following checks substantiate these decisions.

**The fixed-r construction has no hidden generic-line assumption.** Write

    V(X)=(X-1)^k,    v_j=(-1)^(k-j) binom(k,j),  0<=j<k,
    g(X)=a V(X)+h(X),    h_j=g_j-a v_j.

The map from the original integer coefficients to (a,h_0,...,h_(k-1)) is
integral and invertible. Since |g_j|<=H and 1<=a<=H, each h_j lies in
[-(1+|v_j|)H,(1+|v_j|)H]. The product of these fixed-r ranges has O_r(H^k)
labels. For each label, intersect [1,H] with the intervals defined by
-H<=a v_j+h_j<=H, reversing endpoints when v_j<0, then take exact integer
ceilings/floors. The result is one interval, possibly empty. All original
tuples appear exactly once. Fixing a=1 gives (2H+1)^k distinct nonempty
labels, so this full-line algorithm really has a Theta_r(H^k) line charge.

For the d roots alpha_i of monic f, counted with multiplicity,

    P_h(z)=product_i (z V(alpha_i)+h(alpha_i)),
    [z^d]P_h=product_i (alpha_i-1)^k=(-1)^(dk) f(1)^k.

Nonnegative coefficients give f(1)>=A>=1. Thus the leading coefficient is
nonzero on every line, including lines with reducible g, repeated f-roots
or individual zero resultants. None of these makes P_h identically zero.
The signed coefficient is needed for interpolation; its absolute value is
used in the counting argument. Monicity and nonnegativity are substantive
hypotheses, not optional conveniences.

The polynomial primitive may accept reducible f; a subsequent number-field
interpretation may not silently treat that quotient as a field. Ordinary
base-m expansion from N is computable with integer powers and division, but
the actual degree and leading digit must be checked. H014 already describes
the small-input failure and eventual monicity in the intended growing-degree
regime. No all-input field-selection theorem is supplied by H018. Positive
leading g fixes its sign, and degree exactly k is part of the box; lower-degree
elements are not silently included as extra outputs.

**The norm and bit estimates continue to hold as d grows.** For any root alpha,

    |g(alpha)| <= rH max(1,|alpha|)^k,
    |Res(f,g)| <= (rH)^d M(f)^k
                <= (rH)^d (d+1)^(k/2) A^k <= C0.

The middle inequality follows from M(f)<=||f||_2<=sqrt(d+1)A. Rounding k/2
up only enlarges an integral bound. With Q=v/w>=0 fixed rational, w>=1,
the exact threshold is

    p=wd,    T=iroot_p(floor(C0^p/N^v)).

For any integer t>=0, t<=T iff t^p N^v<=C0^p. This proves closed acceptance,
including equality, T=0 and Q=0. The unreduced integer powers have bit widths

    O_(r,eta)(d² log(2H)+d log(2A)+d log(d+1)+n).

Binary search for the integer root is polynomial in these widths. The fixed
rational eta assumption matters; arbitrary real thresholds are not certified
by this argument.

At interpolation nodes z=0,...,d, the coefficients of zV+h have bit widths
O_r(log(2H)+log(d+1)). A padded size-(d+k) Sylvester determinant, or the
determinant of multiplication modulo monic f, gives exact values even when
the second polynomial loses degree. Determinantal minor bounds and factorial
interpolation denominators give polynomial coefficient widths; for example
the loose bound O_r(d²(log(2A)+log(2H)+log(d+1))) suffices for P_h.

Apply the reviewed H014 routine to (P_h-T)(P_h+T): primitive square-free
reduction, exact root isolation, sign-constant gaps and direct integer tests
in boundary intervals. Its degree is at most 2d and all coefficients have
polynomial width. Tangencies, repeated roots, negative leading coefficients
and T=0 are already handled. No fixed-degree real-arithmetic oracle is used.
This proves polynomial work per line plus polynomial work per output, with
polynomial working space and charged output storage. The compact poly(n)
notation requires d, log(2A), log(2H)=poly(n); otherwise those parameters
remain in the polynomial cost. The binomial constants and k label dimensions
cannot be hidden this way if r grows.

This is an extension of the accepted mathematical primitive. There is no
H018 executable to validate, and importing H014's 47 finite cases would not
validate all k or establish any tail population. Primitive filtering costs
gcd work after emission. Any higher-degree irreducibility/usefulness filtering
also occurs after S_all has already been charged.

**The population estimate is only an upper bound.** A degree-d polynomial
with leading coefficient L!=0 satisfies

    #{z in Z: |P(z)|<=T} <= d(1+2rho),
    rho=(T/|L|)^(1/d).

At least one of its d complex root distances must be <=rho, and a disk of
that radius intersects the real line in length at most 2rho. This remains
valid at T=0. In the present construction,

    rho <= rH (d+1)^(ceil(k/2)/d) (A/f(1))^(k/d)
           N^(-Q/d²).

The A factor cancels in the required direction. For fixed r the remaining
factor is bounded by a constant depending on r, or more loosely by poly_r(d).
Multiplying by the label count proves (3). In the stated L scaling it gives
u<=max(ra-Q/delta²,ka) for any distinct attempted subset of these outputs.
Repeated processing of the same element cannot create new independent trials.
Neither the H^k summand nor the first summand is a population lower bound.

**The relaxed optimization is correct in both directions.** Put

    K=k(1+eta),    Q=k(1-eta),
    W=K/delta+a delta,
    u>=b+W/(3b),    u<=max(ra-Q/delta²,ka),
    c>=max(u,ka,2b),    a,b,delta,u>0.

The W expression is the stipulated joint-smoothness model, not a consequence
of norm upper bounds. In particular, unusually small A, coefficient-height
strata and correlations may require a different model. The review accepts
optimization of these real inequalities only.

If u<=ka, then a>=u/k and W>=2 sqrt(Ku/k). Minimizing b+W/(3b) gives
u²>=4W/3, and hence

    u^4 >= 64Ku/(9k),    u³ >= 64(1+eta)/9.

If u<=ra-Q/delta², then a>=u/r+Q/(r delta²), so

    W >= (K+Q/r)/delta+u delta/r
       >= 2 sqrt((K+Q/r)u/r),
    u³ >= 64(K+Q/r)/(9r)
        = 64k[(r+1)+k eta]/(9r²).

At least one branch applies; they need not be disjoint. Their bounds differ
by 64[1+(2r-1)eta]/(9r²)>0, with the second bound smaller. Since c>=u,
the claimed lower bound follows. All divisions and squarings concern positive
quantities, including u>0, and the endpoint cases eta=0,1 are included.

For the reverse direction put L=rK+Q>0, u=c_*, and

    b=u/2,    delta=sqrt(L/u),    a=u(L+Q)/(rL).

Direct substitution gives

    ra-Q/delta²=u,
    W=2 sqrt(uL)/r,
    b+W/(3b)=u/2+4 sqrt(L)/(3r sqrt(u))=u.

The last equality is equivalent to u³=64L/(9r²), the claimed value. Also

    ka<=u  iff  (r-2)Q<=rK,
    rK-(r-2)Q=2k(1+k eta)>0.

Thus all constraints hold with c=u, 2b=u and ka<u. For the non-strict
inequalities this is an attained minimum, hence certainly the stated
infimum. Taking a slightly larger u in the same formulas leaves s=u and
ka<u, while u/2 grows and 4 sqrt(L)/(3r sqrt(u)) decreases. This gives
strict collection slack with c approaching c_* from above.

This argument never uses c>=s. It uses the upper count only through u<=s,
and uses actual attempted work and the explicit full-line charge in c.
For a full enumeration followed by selective processing, c must in addition
pay the actual S_all even if its exponent exceeds u. Dropping that extra
constraint is permissible in a relaxation, not a promise that the modeled
minimum is an actual runtime. At the algebraic witness s=u, but equality in
an upper-count constraint still supplies no elements. Conventional c>=2b
is likewise a stipulated completion model, not a universal linear-algebra
lower bound. These qualifications prevent the sufficient-envelope/necessary-
cost error raised in the brief.

**The degree and constant comparisons survive.** Removing 64/9 from c_*³
gives

    F(r)=(1+eta)-2eta/r+(eta-1)/r²,
    F'(r)=2eta/r²+2(1-eta)/r³>0.

For eta in [0,1] at least one derivative term is positive. The expression
also increases with eta. At eta=1 it becomes the unfiltered Card C value
128(r-1)/(9r). At r=6, eta=0 the comparison is

    560/81 > (92+26 sqrt(13))/27,
    equivalently 142>39 sqrt(13),
    with 20164>19773 after squaring positive sides.

Consequently the r>=6 exclusion is valid in this relaxation, and r=2 is its
best dimension at any fixed eta. Neither conclusion compares actual useful
populations or replaces H017's separate question.

For the specified r=2 witness,

    K/delta+a delta=9/7+7/5=94/35,
    W/(3b)=376/399,
    u_required=19/20+376/399=15101/7980,
    s=93/49,
    s-u_required=313/55860>0,
    2b-s=1/490>0.

The line exponent is a=1<s. Thus max(s,a,2b)=19/10 is the stated sufficient
conditional envelope. Enough actual candidates and all processing/completion
premises are still required to realize it.

The parent contains one arithmetic typo in its comparison proof. Exactly,

    (19/10)^3 < (92+26 sqrt(13))/27
    iff sqrt(13)>93193/26000,
    13*26000²=8788000000 > 93193²=8684935249.

Replace 93203 and its square by these numbers, or replace the parent's word
“equivalent” by “implied by.” Its stronger displayed inequality with 93203
is also true, so the desired strict comparison was not endangered.
The comparison constant and its square-congruence scope were checked directly
in [Lee–Venkatesan, Remark 4.31](https://arxiv.org/html/1805.08873v1).
That source is not an unconditional general factor-extraction theorem.

**The linear enumeration formulas are exact.** To separate the coefficient
from the asymptotic parameter a, write g=xX+y, 1<=x<=H, |y|<=H. Then
beta=x+y runs from 1-H to 2H, exactly 3H labels, and

    max(1,beta-H)<=x<=min(H,beta+H).

Every label in this minimal range is nonempty. Wider ranges may contain
charged empty lines. For x!=0,

    Res(f,xX+y)=(-1)^d x^d f(-y/x),
    P_beta(x)=sum_(i=0)^d f_i (-1)^(d+i) (beta-x)^i x^(d-i).

The latter polynomial identity also covers interpolation at x=0. Its leading
coefficient is (-1)^d sum_i f_i=(-1)^d f(1), not just the contribution from
the monic term. Binomial expansion takes O(d²) coefficient arithmetic with
polynomial widths. At eta=4/5 the exact acceptance rule is

    |P_beta(x)|^(5d) N <= [(2H)^d(d+1)A]^(5d).

The gcd(x,y)=1 filter removes contents; a primitive nonconstant linear
polynomial is irreducible over Z, and x>0 fixes its sign associate. This does
not prove distinct ideal rows or useful dependencies. Zero resultants and
zero rational values are not ordinary smoothness successes. A valid
irreducible f of degree d>1 rules out a common linear factor, but the
enumerator's wider polynomial domain does not assume irreducibility.

**Homogeneity supports the proposed conditional test, with a real-set wording
correction.** Define F_f(z)=Res(f,g_z) on real coefficient vectors, and put

    C_f=r^d(d+1)^ceil(k/2) A^k,
    U=C_f H^d N^(-Q/d),    T=floor(U),
    epsilon=N^(-Q/d²),    R=H epsilon>0,
    B_f={z: |F_f(z)|<=C_f}.

Since F_f(Rz)=R^d F_f(z) and U=C_f R^d, the exact identity is

    {z in R^r: |F_f(z)|<=U}=R B_f.

For integer z, integrality of F_f(z) gives |F_f(z)|<=U iff |F_f(z)|<=T.
Thus clipping R B_f to the original coefficient box and taking its lattice
points gives exactly the enumerator's accepted set. However, the *real*
sublevel |F_f(z)|<=T need not equal R B_f. Section 4's reference to the
“real sublevel set of (2)” should explicitly say “the unfloored real
threshold corresponding to (2).” Its next sentence about integer acceptance
already supplies the intended repair. No lattice count or cost changes.

Assume, without asserting it, that the proposed bound

    S_all <= exp(o(D)) (R^r+H^k)

holds uniformly for the actual varying f and d and the population being
modeled. Then s is replaced by max(ra-rQ/delta²,ka). The ka branch still
implies u³>=64(1+eta)/9. In the other branch,

    a>=u/r+Q/delta²,
    W>=(K+Q)/delta+u delta/r,
    K+Q=2k,
    u³>=128k/(9r).

Because either branch may apply, the valid combined conclusion is

    c³>=u³>=min(128(r-1)/(9r),64(1+eta)/9)>=64/9.

This is exactly the claimed conditional obstruction. It requires no
attainment argument for this new relaxation. It does require the same joint
smoothness law and B-scale collection obligation; it is not a bound on a
changed stratified model or on factoring.

No reason to accept the assumed lattice estimate follows from dilation alone.
Unbounded cusps, repeated or nearly coincident forms, small coefficient-height
strata, primitive restrictions, coefficient dependence and lattice discrepancy
all remain relevant. A fixed-f finite-volume theorem would not supply a
uniform exp(o(D)) constant for the ordinary-base family. In particular,
d log d=(delta/3+o(1))D in this scaling: even d^(C d) losses with fixed C>0
would change the leading constant. Polynomial factors in A can be still
larger. The report correctly warns about these issues and does not prove or
assume away their geometric content. No general supply theorem is attempted
in this review.

**The surviving next test is quantitative primitive supply for this fixed
linear family.** Freeze r=2, eta=4/5, a=1, b=19/20 and delta=7/5; use the
N-only ordinary-base rule with explicit checks for degree, monicity and any
field requirements. On the family actually claimed, consider

    M_N = #{(x,y): 1<=x<=H, |y|<=H, gcd(x,y)=1,
                  g=xX+y, g(m)!=0, Res(f,g)!=0,
                  |Res(f,g)|^(5d) N <= C0^(5d)}.

The current bound gives only M_N<=S_all<=L[1/3,93/49]. Under the unchanged
joint law, the necessary attempt exponent is 15101/7980. A uniform upper
bound with exponent at most 15101/7980-kappa for any fixed kappa>0 would
falsify this witness *within that law*. A lower bound on M_N with exponent
at least 15101/7980+kappa, where 0<kappa<313/55860, would clear the primitive
population hurdle only; it would still need the joint yield, independence
and completion obligations. Equality of leading
exponents alone does not establish a strict collection surplus.

For a particularly concrete negative target, the proposed sharper count at
these parameters would give

    R=L[1/3,44/49],
    s_sharp=max(88/49,1)=88/49,
    15101/7980-88/49=5387/55860>0.

Its proof on the required linear population would therefore reject this
witness under the unchanged model. This specialization is only substitution
into the conditional calculation, not evidence for the count. A different
upper bound below the necessary threshold would suffice; a broad theorem
for every r is unnecessary for the next test.

The supply study must state its input quantifiers and account for zero norms,
primitive losses, varying coefficients, cusps and the actual growing degree.
If smaller-height or much smaller-norm strata drive the supply, recompute
their rational and algebraic norm law and collection costs instead of applying
the full-height W expression to them. Special units, fixed-degree volume
estimates and tiny-H admission ratios would not resolve this test. H016 still
owns paid processing, and H017 still owns its quadratic-tail question.

Only this report and adjacent H018-review-provenance.json are written. No
shared code, Lean, STATE, registry, parent report, hypothesis or frozen evidence
was changed; no packages, delegation, commits, publication or scheduler were
used. No finite experiment, numerical sweep or candidate execution was needed.
Read-only hashing is provenance work, not a registered research run. Shared
build checks were not run because this is a document-only review.

No new substantive supply, geometry or complexity lemma is claimed beyond
the assertions submitted for review. The displayed derivations verify those
assertions; the arithmetic and real-set corrections are local repairs. Any
future result proving the proposed count or useful supply will need a new
independent review. Input hashes and the reviewed report version are recorded
in [provenance](H018-review-provenance.json). Verified full factoring
complexity improvement remains **NONE**.
