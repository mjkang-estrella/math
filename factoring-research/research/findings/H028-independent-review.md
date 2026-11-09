# H028 — Independent mathematical and full-cost review

2026-10-08. **ACCEPT the symbolic identities, the balanced-model optimum and
the two “no new survivor” dispositions. CORRECT the localized accounting and
quantifier statements identified below before adopting the report as a reusable
full-cost ledger. Verified full factoring complexity improvement: NONE.**

This reviews all 808 lines of the frozen submitted draft, SHA-256
`e493c11555e6285c88caf8ab970c367d387f520263e8157b981f246d96b1152d`.
Line references below refer to those bytes, not a subsequently edited report.
The exact constant and every displayed algebraic identity survive review.
There is no new general factoring theorem, many-field lower bound, smoothness
law, field-selection guarantee, or productive-split guarantee.

Three localized repairs are needed: distinguish the attempted index interval
from its surviving fields; charge filtering of discarded records, not only final
R; and give the general expected-supply/cost formula explicit strategy and
expectation quantifiers. These repairs do not improve either card or change
the optimum. Exact replacement text appears in Section 10.

## 1. Evidence boundary and source access

Before evaluating the claims I copied the submitted draft, intake, hypothesis,
proposer manifest, project instructions/checkpoint, relevant dependencies and
archived sources into [H028-review-inputs](H028-review-inputs/). Their byte
lengths, SHA-256 values and capture timestamps are recorded in
[H028-review-inputs.json](H028-review-inputs.json). Review used these copies.
The proposer manifest itself matches
`5598e8b68cbefa4023dc01eec43c4bf730ee1500bcc75ee5d7e407882ba2852b`.
Its original input hashes remain completion-time evidence; they have not been
retrospectively renamed read-time seals. The review copies supply a new seal.

Read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, all of the captured STATE, H028's hypothesis and intake,
and the provenance manifest. Read the relevant W001 baseline/relation entries,
H016 disposition and integer/ideal/cost sections, H022 disposition and the
current conditional model with its review's strategy/mesh repairs, and H023
disposition and special-family comparisons. Unused frozen supporting material
is preservation, not a claim that every line of every dependency was audited.
The user-supplied live-task status overrides the stale STATE. No other task was
polled, duplicated, or delegated.

I independently retrieved all five cited primary documents. Every retrieval
returned HTTP 200 and exactly matched the corresponding frozen proposer
source. Downloads, extracted text and
[the access log](H028-review-source-access.json) are review-owned artifacts.
The Springer response URL acquired a cookie-related query string, but the
response was the complete PDF with the matching hash, not an access-error page.
No paywall or inaccessible section prevented the requested inspection.

- [Coppersmith, §§3–4](https://link.springer.com/content/pdf/10.1007/BF00198464.pdf):
  inspected printed pp. 174–180, with §2's reconstruction/cost background.
  Inspected the archived page images for pp. 175, 177 and 178 to resolve OCR.
  The family, matrix blocks, Stage-2 processing charge, optimized parameters
  and factory boundary are supported. The paper expressly describes its
  structured-value smoothness substitutions as heuristic.
- [Lee–Venkatesan, v1](https://arxiv.org/html/1805.08873v1): inspected
  Theorems 2.1/2.3/2.6, Remarks 2.7/4.31, §6's character and square-extraction
  discussion, and §7's useful-congruence qualification. Remark 4.31 gives the
  submitted exact constant. This is a randomized variant, not a yield theorem
  for the fixed coefficient line (2.1). Its fruitful-congruence statement has
  the stated Blum-semiprime/conjectural restriction.
- [Stevenhagen, §§6–10](https://pub.math.leidenuniv.nl/~stevenhagenp/ANTproc/04psh.pdf):
  supports the separation of order/ideal/class/unit obstructions, character
  columns, the derivative multiplier, and actual root extraction. His brief
  noninvertibility discussion must not be interpreted as making gcd=N a
  proper factor; H028 correctly does not make that inference.
- [Kleinjung, §6.7](https://www.joppebos.com/montgomery/book_ch6.pdf):
  printed pp. 11–13 describe rotations and sieving over their index, including
  prime-power considerations. H028 distinguishes root scoring there from its
  complete norm processing. The attribution is appropriately limited.
- [Pomerance](https://math.dartmouth.edu/~carlp/PDF/qs08.pdf): inspected
  the quadratic-congruence algorithm, full exponent reconstruction, sieve and
  sparse-matrix discussion, and printed p. 80 on multiple polynomials.
  This supports the classical comparison, not an unconditional yield law for
  H028's positive quadratic sequence.

The HTML-to-text extraction keeps mathematics from MathML `alttext`; the
complete HTML is retained. PDF text has OCR/encoding defects, particularly in
equations. The cited page images and independent derivations resolve the
constants at issue. This is targeted primary-source inspection, not exhaustive
priority research or a new audit of every theorem in those sources.

## 2. Claim-by-claim decisions

1. **ACCEPT:** eventual monicity of the base-m construction, actual coefficient
   heights, norm identity and V-scale envelopes, lines 79–135. **CORRECT** the
   use of K as an index bound when extra attempts Q are used; see repair P1.
2. **ACCEPT conditionally:** the rational/algebraic smoothness exponents,
   balanced K, (field,p,root) columns and collection equation (2.8). These
   reconstruct a stated heuristic model, not actual uniform useful yield.
3. **ACCEPT:** explicit K*M norm accounting, H016's width qualifications,
   good-prime direct labels and paid root-table alternatives. Bad-prime losses,
   character construction, late failures and storage remain separate charges.
4. **ACCEPT:** (2.9)–(2.10), including the derivative multiplier and its unit
   condition. Ideal parity alone is insufficient. A valid congruence alone
   is insufficient for proper splitting.
5. **ACCEPT:** the global optimization (2.12)–(2.15), including boundaries
   and the equality witness. Both discarded costs are strictly subdominant at
   the optimum of this balanced model. **REJECT** a factoring or unrestricted
   multi-field lower-bound interpretation.
6. **ACCEPT:** the separately costed factory constants and amortization
   boundary. They are not a cold 1.6386 bound.
7. **ACCEPT:** Card A's exact progression sieve, full-valuation cases and
   costs for a contiguous pool. **CORRECT** the cost/index notation after
   rejected polynomials leave gaps. Accept its processing-only closure.
8. **ACCEPT:** (3.5), with degree/height/construction charges and no automatic
   favorable yield change.
9. **ACCEPT:** the common-order square-map lemma and norm-map compatibility
   objection. Neither is a new method for finding useful maps.
10. **ACCEPT:** the N=55 witness, including irreducibility, good prime 43,
    derivative units and nonsquare field elements. **REJECT** interpreting it
    as a failure of an implementation that still checks adequate characters
    or verifies square roots; it refutes the unqualified valuation merging.
11. **ACCEPT:** the coefficientwise primorial lower bound, actual norm lower
    bound and giant aggregate bit mass for the specified construction.
12. **ACCEPT:** compatible isomorphisms and the same-field translation
    calculation, without crediting representations as independent supply.
13. **ACCEPT:** paid prime construction, distinct quadratic fields, the direct
    integer square map and full parity reconstruction in (4.6)–(4.8).
14. **ACCEPT:** duplicate/provenance and zero-derivative qualifications, and
    (4.9)–(4.11) as a conditional size/yield model. Its sqrt(2) constant is an
    infimum of that model, not a achieved factoring bound.
15. **ACCEPT:** the negative-sign QS comparison only as prior-art comparison.
    **REJECT** importing QS yield or L[1/2,1] into every multiplier/b family.
16. **CORRECT/ACCEPT after P2–P3:** Section 5's schematic supply/cost ledger.
    Its algebra is correct; discarded-input cost and expected-work quantifiers
    need explicit definitions before reuse for adaptive or random-size work.
17. **ACCEPT:** zero new survivors for the actual cards. **REJECT** any
    exhaustive novelty claim or all-algorithms exclusion. No experiment is
    warranted merely to confirm these symbolic calculations.

## 3. Base family, norm objects and complete reconstruction

Write t=log N, D=t^(1/3)(log t)^(2/3), V=t^(2/3)(log t)^(1/3),
with fixed delta,epsilon>0 and beta>=gamma>0. Then dD=(delta+o(1))V,
log m=(1/delta+o(1))V, and D=o(V). Since d/m tends to zero,

    (m+1)^d/m^d <= exp(d/m) < 2

eventually. The floor definition gives m^d<=N<(m+1)^d, so the leading base-m
digit is exactly one. The finite exceptions are not covered by this eventual
argument; H028 explicitly charges their treatment.

For a contiguous pool indexed 0<=i<J, only the linear and constant
coefficients change. They are c_1+i and c_0-im, with 0<=c_j<m in f_0.
Consequently

    H(f_i) <= (J+1)m+J,
    |c_0-im| >= (i-1)m for i>=2,
    log H(f_i) <= log m+log(J+2)+O(1).

The submitted K bound is therefore correct for its displayed pool J=K.
If validation tries Q consecutive indices to retain K fields, J=Q is the
correct bound. Q need not equal K, and the retained indices need not be
consecutive. If Q=L[kappa+o(1)], the change remains o(V) and has no leading
effect on the current optimization. Without that assumption it must be paid.
Counting Q attempts is not proving that Q of this size suffices. Nor does
irreducibility ensure distinct isomorphism classes or useful relation supply.

For each retained monic irreducible f_i and primitive pair with b>0,

    Norm(a-b alpha_i) = product_j(a-b alpha_(i,j))
                       = b^d f_i(a/b)
                       = F_0(a,b)+i b^(d-1)(a-mb).

Since E/m tends to zero, m-E<=|a-mb|<=E(m+1). Thus the rational leading
V coefficient is uniformly 1/delta in this box. The algebraic bound is

    |F_i(a,b)| <= (d+1)H(f_i)E^d,
    log |F_i| <= (1/delta+epsilon delta+o(1))V

when log J=O(D). It is an upper envelope, not an assertion that every norm
attains it. The rational/algebraic smoothness substitutions remain assumptions
about the actual streams, with correlations and exclusions included.

All retained-field pairs yield K*M norm objects in the described explicit
stream, even if most are nonsmooth. Norms examined before a later field or
character failure also count. Polynomial descriptions do not eliminate these
objects from an explicit-list algorithm.

For clarity, H016's aggregate bound can be carried here with

    P = sum_(p in the used integer bases) bitlength(p),
    U = sum_(all nontrivial norm inputs) bitlength(|F|),
    S = number of processed scalar records,
    I = total identifier/provenance/payload bits,
    b_total = 2+P+U+O(S), L0=max(1,log2(b_total+2)).

Its conservative bit bound has the form

    O(B log^3(B+2) + b_total L0^4 max(1,log L0)
      + (I+1)log^2(I+b_total+2)).

Here B covers the used prime ranges. This reduces to (B+S)poly(n) only with
polynomial scalar, payload, log B and log S widths. Product-tree nodes may
have aggregate-sized operands; their cost is already in this formula. Output
vectors and retained rows are additional storage, not constant-size objects.

For a prime p dividing a monic linear-element norm, p|b would imply
F_i(a,b)=a^d mod p, contradicting primitivity. Hence b is invertible and
rho=a/b mod p is the sole root relevant to that element. At p not dividing
disc(f_i), local maximality and square-free reduction imply

    v_(p,rho)(a-b alpha_i)=v_p(F_i(a,b)).

No other ideal over p divides that element. This gives deterministic direct
labeling per recovered support entry for these linear elements; it does not
require an all-root table or extend H016's quadratic case to bad primes.
The label includes i. Full tables alternatively cost expected K*B_A poly(n),
or the conservative deterministic K*B_A^2 poly(n), with joins/access paid.
Discarding norms meeting disc(f_i) is exact but has unquantified useful-supply
loss. Factoring a discriminant, constructing a maximal order and supplying
enough characters are not included merely by computing the discriminant.

Balancing K*B_A' with B_R' gives kappa=beta-gamma and dimension L[beta].
For general multiplicity the conventional ambient scale is
q=max(beta,kappa+gamma). This counts columns; it is not a rank theorem.
Polynomial-width norms and polynomially many character/sign coordinates per
field give polynomial row weight. With R=L[q] rows and W=R poly(n), the
charged sparse model is D_mat*W=L[2q]poly(n). Filtering must retain lifting
records; fill, failed linear-algebra attempts and duplicates do not disappear.

For (2.9), the rational sign and full prime exponents really construct Y.
Each field separately needs z_i^2=U_i; its even ideal valuations do not imply
that a principal square generator exists or that its unit is square. A square
root z_i of integral U_i is integral. The order multiplier gives
h_i=f_i'(alpha_i)z_i in Z[alpha_i]. After exact verification of
h_i^2=f_i'(alpha_i)^2 U_i, reduction alpha_i->m is legitimate. For unit
d_i=f_i'(m) mod N it yields x_i=h_i(m)/d_i and then X=product x_i, with
X^2=Y^2 mod N. A proper gcd of d_i with N is a valid early split; gcd=N is
a failed inversion. One cannot extend the order map to arbitrary fractions
without this denominator check.

For a d_i multiplier or a field root, the required representations may have
R_i poly(n) bits, rather than one residue's n bits. The conventional allowance
K*B_A^2 in (2.11) is appropriate only with R_i=L[gamma]poly(n) and the
stated root/completion model. No arbitrary-degree or arbitrary-population root
algorithm has been proved to satisfy it here. H028 correctly asks to recharge
sum_i T_root(i,R_i) outside that setting.

For a k_i-dimensional square-class obstruction space, uniform independent
dual characters would give failure at most 2^(-e) with k_i+e samples. Taking
e>=log2 K+log2(1/eta) controls a union failure eta. This explains the extra
O(log K) conditional allowance. It does not construct such samples. In
particular, the different character sampler discussed by Lee–Venkatesan
cannot be silently substituted into a polynomial-width free-character model.

If N is odd with omega>=2 distinct prime factors and Y is a unit, a uniform
CRT square-root sign vector succeeds except for the two global sign patterns:
probability 1-2/2^omega>=1/2. H028 does not prove this distribution. Choosing
the signs of algebraic roots z_i independently only changes X by an overall
sign; it supplies no CRT root entropy. Actual proper-split probability remains
sigma_N. Uniform per-input success and full costs are needed to extend a
splitter through primality checks and the polynomial-size factor tree.

## 4. Independent derivation of (2.8)–(2.15)

The modeled Stage-1 population is M=L[mu], mu=2epsilon-tau_R, where
tau_R=1/(3delta beta). Each field's algebraic test has assumed penalty
tau_A=(epsilon delta+1/delta)/(3gamma). Requiring its conventional quota
L[gamma] gives exactly

    epsilon(2-delta/(3gamma))
       >= gamma + 1/(3delta beta) + 1/(3delta gamma).       (R1)

This is (2.8). Its right side is strictly positive. Since epsilon>0,
feasibility forces delta<6gamma; equality is also infeasible. A count of
expected rows is not by itself probability of reaching the quota.

The four cost exponents in (2.11) are respectively the rational box scan,
the conventional sparse matrix, all second-stage norms, and conservative
per-field roots/root tables:

    2epsilon, 2beta, kappa+mu, kappa+2gamma=beta+gamma.

Generation with Q=L[kappa+o(1)], integer bases, expected root tables and
ordinary row recording fit below these terms, under the declared completion
and width assumptions. The envelope does not prove those assumptions.

Drop the last two terms and let its bound be 2x. Then x>0,
epsilon<=x and gamma<=beta<=x. The left minus right of (2.8) has derivatives

    d/d epsilon = 2-delta/(3gamma) > 0,
    d/d beta = 1/(3delta beta^2) > 0.

Increasing epsilon and beta to x preserves feasibility, keeps beta>=gamma,
and leaves delta<6gamma unchanged. Multiplication by positive 3gamma gives

    3gamma(2x-gamma) >= x delta+(1+gamma/x)/delta.

For positive delta, AM–GM makes the right side at least 2sqrt(x+gamma),
with equality iff delta^2=(1+gamma/x)/x. All quantities squared next are
positive, because 0<gamma<=x. Setting z=gamma/x therefore yields

    x^3 >= H(z):=4(1+z)/(9 z^2(2-z)^2), 0<z<=1.

An explicit logarithmic derivative is

    H'(z)/H(z) = (3z^2+2z-4)/((1+z)z(2-z)).

The denominator is positive. The numerator increases strictly on this
interval, is negative at zero and positive at one, and vanishes only at
z_*=(sqrt(13)-1)/3. Moreover H(z) tends to infinity as z->0+ and
H(1)=8/9. Thus this stationary point is the unique global minimum, including
the closed endpoint z=1. That endpoint gives c^3=64/9, not a better value.
There is no omitted small-gamma boundary escape at bounded x. Taking
delta->0 with bounded x violates the positive reciprocal term, while
delta>=6gamma already fails (R1).

Let s=sqrt(13). Substitution gives

    x^3=(46+13s)/108, epsilon=beta=x,
    gamma=x(s-1)/3, delta=x(4s-10)/3,
    kappa=x(4-s)/3.

The two positive expressions for delta, namely the displayed one and the
AM–GM equality delta^2=(1+z_*)/x, agree. For example, use
3z_*^2+2z_*=4 to simplify either side. All parameters are positive,
gamma<beta, and delta<6gamma. These are feasible equality parameters, not
merely a necessary-bound minimizer outside the admissible set.

For additional exact checks, the identities reduce to

    6delta*x*kappa=1,
    x delta+1/delta=3gamma^2.

The first follows from
(46+13s)(13s-46)=81; the second follows by the same substitution.
Consequently

    tau_R=2kappa, tau_A=gamma,
    mu=2x-2kappa=2gamma,
    mu-tau_A=gamma.

Thus both dropped exponents are beta+gamma=x(1+z_*)<2x, whereas the first
two equal 2x. The relaxed bound is attained by the full displayed envelope,
and

    inf c = c_C=2x,
    c_C^3=(92+26sqrt(13))/27.

If strict positive quota slack is required, increase epsilon slightly with
the other equality parameters fixed. Its positive derivative in (R1) makes
collection strict and the continuous cost tends back to c_C. Hence this
remains the infimum in the strict limiting model. It is not an attained
algorithmic yield law. Unbounded or size-dependent parameter families need
their own uniform asymptotics rather than this fixed-constant proof.

The result is precisely the known balanced-model constant. Erasing norm
processing and roots leaves the same infimum because the rational scan,
quota model and matrix charge already force it. None of those three has
been established as a universal necessity of many-field factoring.

## 5. Factory setup and amortization

Set b=((5+2sqrt(6))/18)^(1/3), beta=gamma=b,
epsilon=b sqrt(6)/2 and delta=3b(sqrt(6)-2). Direct substitution gives

    tau_R=b(sqrt(6)-2), tau_A=b,
    mu=2epsilon-tau_R=2b, kappa=0.

For example 9b^3(sqrt(6)-2)^2=1 verifies the first identity. Thus the
stored Stage-1 table has exponent 2b, the remaining norm/matrix/root model
has exponent 2b, and the table's initial box scan has exponent 2epsilon.
These yield the submitted values approximately 1.6386 and 2.0068.

One table must use fixed, applicable m,E and prime-bound data for its input
range. Replacing m independently for each N would discard its amortization.
For Q_f applicable inputs, total work is setup plus Q_f times per-input work,
with storage and access charged. If Q_f=L[nu], the average leading envelope
is max(2epsilon-nu,2b). Reaching the smaller exponent requires
nu>=2epsilon-2b, besides actual applicability and completion assumptions.
Cold Q_f=1 retains the setup. No factory bound improves either card's cold
comparison, and the factory's rational table is not an all-algebraic-root table.

## 6. Card A: exact index processing and its scope

For a fixed paid pair, U=F_0 and V=b^(d-1)(a-mb) are integer inputs of
polynomial width in the baseline regime. Eventually a-mb cannot vanish,
so V is nonzero. Distinct indices give distinct signed integers U+iV;
absolute values, norms of other pairs and relation equations still need
their actual duplicate treatment.

For p not dividing V, exactly one class i=-U/V mod p is divisible by p.
For p|V, either no value is divisible (p does not divide U), or every
value is divisible (p|U). In the latter case valuations are not necessarily
equal. One can set h=min(v_p(U),v_p(V)), divide the progression by p^h,
and continue; cancellation can increase particular entries' valuations.
The submitted alternative of exact division at each nonzero hit is sufficient.
Zero entries must be removed before any “divide until indivisible” loop.

There is a useful additional consistency check for this particular family.
If p|b, then U=a^d mod p is a unit. If p|a-mb, primitivity gives p not
dividing b and U=b^d N mod p. Hence p|U and p|V imply p|N. An associated
proper gcd can be returned, but this does not justify omitting the full
valuation case from a general progression processor or calling gcd=N success.

For a contiguous interval of length J, ordinary first hits cost at most

    J sum_(p<=B_A) 1/p + pi(B_A).

There are at most bitlength(|V|) distinct exceptional primes dividing V.
Their full-array passes and all repeated divisions add polynomial-width
factors. Building/reading the residual arrays costs J per pair as well.
Thus (M*B_A+M*J)poly(n) is a valid conservative bound. The factor M*B_A
cannot be dropped from the literal per-pair full prime scan.

For an all-valid contiguous pool J=K this is exactly (3.2). After Q
consecutive attempts yield a subset I of size K, the same loop scans J=Q
positions and needs a membership filter. Relabeling surviving indices
0,...,K-1 would change their polynomials and destroy U+iV. This is repair P1.
The H016 alternative can instead enumerate only the retained, explicitly
indexed K values per pair, with its original (B_A+K*M)poly(n) bound.
Neither option makes failures, actual index widths or family selection free.

At the optimum, the direct scan term is mu+gamma=3gamma>2beta because
3gamma/beta=sqrt(13)-1>2. H016 removes that scan but retains mu+kappa=
beta+gamma<2beta. The optimization in Section 4 already permits zero
second-stage cost. Therefore a change confined to this processor cannot
lower that model's optimum. It can improve polynomial factors or engineering
cost; it does not change the reviewed leading constant.

For f_i=f_0+i*g with deg g<d, its leading coefficient stays one,
H(f_i)<=H(f_0)+J H(g), and b^d g(a/b) is integral. The submitted
homogenized identity is correct. The common modular root follows from
g(m)=0 mod N. Neither this congruence nor compact notation proves smaller
norms, low-height g, cheap construction or useful supply. Higher-degree g
requires a fresh degree/leading-coefficient/denominator analysis. The closure
is only for unchanged norm/yield/scan/matrix assumptions, not every rotation.

## 7. Card B: compatibility and the field-label witness

For (4.1), multiplicativity gives

    psi(w)^2 = product psi(v_j)
              = (product r_j)(product c_j)^2
              = y^2(product c_j)^2.

Every c_j is a known unit, so dividing proves (4.2). If w lies in a larger
order or a fraction ring, the reduction domain and denominators must first
be justified. Taking identical rational v_j=r_j and the directly chosen
root w=y just returns a tautology. The lemma supplies neither suitable
inputs nor a probability of a useful output.

For a quadratic root alpha of X^2+sX+t, conjugation gives
Norm(a-b alpha)=a^2+sab+tb^2. Expanding
(a-bm)(a+b(s+m))+b^2 f(m) gives the same integer. Modulo N this is r
times a second factor, not r times an already known square. When r is
a unit it is literally the missing ratio; nonunits require gcd handling.
Norms preserve squares multiplicatively but are not the needed reduction
homomorphism from the selected field embedding.

For the explicit witness, note 2364=55*43-1. Therefore

    f_0(4)=55, f_1(4)=55+4*55*43=55*173,
    f_0,f_1 mod 43 = X(X-1),
    f_0'(4)=7, f_1'(4)=7+55*43.

Both derivatives are units modulo 55. The first discriminant is -171;
the second is 2364^2-172, strictly between consecutive squares
2363^2 and 2364^2 because 2*2364-1>172. Thus both polynomials are
irreducible. Their fields are distinct: one is imaginary and the other real.
Both discriminants are 1 mod 43, so p=43 is good. The root-zero ideals
have residue degree one. The element -alpha_i has norm 43, lies in its
own root-zero ideal but not the root-one ideal, and has valuation exactly one.

If -alpha_i were z^2 in its field, its norm would be Norm(z)^2 in Q,
contradicting 43 being nonsquare in Q. The rational values are each -4,
and their product is 16; the norm product is 43^2. A merged valuation-only
matrix loses exactly the separate odd ideal coordinates. It cannot infer
two field roots from this two-row dependency.

This is a hand-checked algebraic counterexample, not an experiment. Adequate
fieldwise characters or explicit square-root verification would reject this
false candidate. The witness is not a claim that every implementation which
compresses some ideal data fails, or that all characters must miss the example.
Its narrow claim, and the submitted wording at lines 523–530, are correct.

## 8. Shared reductions, giant widths and same-field maps

If distinct integer polynomials are coefficientwise congruent modulo P,
some coefficient difference has magnitude at least P. If both heights were
strictly below P/2 this would be impossible. This establishes the general
coefficientwise-congruence statement with its strict endpoint.

For the specific f_i=f_0+iP(X-m), P is the primorial through B_A.
The prime number theorem gives log P=theta(B_A)~B_A, and the changed
constant coefficient is c_0-iPm, so its width really increases. Mod-p
root tables agree for base primes; lifts modulo p^k and field ideals need
not agree. Table equality therefore does not prove common algebraic columns.

For the given box, V=b^(d-1)(a-mb) is a nonzero integer. Thus for i>=1,

    |F_0+iPV| >= P-|F_0| >= P/2

eventually, because log |F_0|=O(V_scale) whereas log P is of order
B_A=exp((gamma+o(1))D), which dominates V_scale. Here V_scale denotes
the asymptotic scale V of Section 3, not this paragraph's progression step.
This is an actual lower bound, so it does not confuse an upper height bound
with realized norm size. In the original parameter regime every changed
norm has Theta(B_A) bits up to polynomial factors. Its explicit norm list
has aggregate scale K*M*B_A; explicit polynomial storage also costs
K*B_A times polynomial factors. H016's aggregate theorem still applies,
but its polynomial-scalar-width corollary does not. Compact coefficients or
processing just a smaller prime core require a different charged algorithm;
the argument is not a lower bound for every implicit representation.

A unital homomorphism of number fields is injective and fixes Q; equal
degrees make it an isomorphism. Transporting elements/ideals through such a
map is legitimate only with constructed maps commuting with the modular
reductions. For f_i(X)=f_0(X-iN), alpha_i=alpha_0+iN and

    a-b alpha_i=(a-iNb)-b alpha_0.

The coefficient of X^(d-1) is c_(d-1)-diN. For nonzero integer i,
b>=1 and |a|<=exp(O(D))=o(N), the old first coordinate has magnitude
at least N-o(N). This is an enlarged old element region, not a new supply
at the old coordinate height. There could be useful elements in a changed
region, but these maps alone do not prove that. Shifting by i instead moves
the modular root to m+i and changes the rational value as the draft says.

## 9. The positive quadratic construction and its model

After ordinary preprocessing, let h=K+n. A sieve to an O(h log(h+2))
prime bound and gcd tests gives the first h primes at h poly(n,log h)
cost. Since N has at most n distinct prime divisors, this suffices for K
distinct coprime ell_i unless a tested prime already gives a proper split.
The first h primes have logarithmic height O(log(h+2)). This is a paid
uniform construction; no factor of N or primality oracle is supplied.

For positive ell_i,N, X^2+ell_i N is monic with no rational root.
Quadratic fields Q(sqrt(-ell_i N)) coincide only if ell_i/ell_j is a
rational square; distinct primes preclude this. The coefficient height is
exactly ell_i N, and the common order maps alpha_i->0 exist modulo N.
They are not the ordinary derivative-invertible NFS pipeline, since f_i'(0)=0.

Direct multiplication instead gives

    q=(a-b alpha_i)(a+b alpha_i)=a^2+ell_i N b^2,
    q=a^2 mod N.

Thus each q comes with its known modular square root a. On unit rows this
can even instantiate (4.1) with A=Z, v_j=q_j, r_j=1, c_j=a_j mod N.
Nonunit a_j receives a paid gcd check; it is not inverted silently.
The construction does not assert a square root of a-b alpha_i in its field.

If full integer exponents sum to even values over a selected set, then
Y=product_p p^(sum_j v_p(q_j)/2) mod N and X=product_j a_j mod N
satisfy X^2=Y^2 mod N. All q are positive, so this integer base needs no
negative-sign column. It requires no algebraic ideal/character/root algorithm.
Returning a proper gcd still requires verification and sufficient productive
dependencies; irreducibility does not supply them.

Tuple provenance and the actual root a mod N matter. Repeating the same
(q,a mod N) twice gives X=a^2=q=Y mod N and a tautology. Different roots
of the same q may give a proper split, or just opposite signs and another
tautology; test both gcds. Distinct q or distinct exponent rows also do not
prove useful independence. All rejected nonprimitive candidates and duplicate
equations must remain in their enumeration/filter cost. If enumeration visits
the full A-by-H box before its gcd filter, M is that raw box count; if a
primitive-pair generator is used, its construction and rejected work are paid.

Let w bound the bit length of q and the retained scalar payload. Then

    w = O(n+log ell_max+log(A+2)+log(H+2)),
    log ell_max = O(log(K+n+2)).

Integer processing and provenance require (B+K*M) times polynomial factors
in these widths and index lengths. Reconstructing from R selected full
factorizations costs R poly(n,w,log B,log R), with total exponent/support
storage charged. This specializes to the submitted R poly(n,log B,log R)
when all candidate scalar and payload widths are poly(n). Arbitrarily larger
widths must remain explicit; they cannot be hidden by the n notation.

With a,b>=1 the bound N<=q<=A^2+ell_max N H^2 is immediate.
If log A,log H,log K=o(t), then log q=(1+o(1))t uniformly. For
B=exp((b+o(1))D), the size-model smoothness parameter is

    u_sm=log q/log B=(1/b+o(1))t^(2/3)(log t)^(-2/3),
    u_sm log u_sm=(2/(3b)+o(1))V.

This proves the submitted model calculation (4.10). Because V/D tends to
infinity, L[1/3,u] explicit attempts with that assumed rate cannot meet the
L[1/3,b] quota. It is not an upper-smoothness theorem about this sequence.

At L_N[1/2], put D2=sqrt(t log t). The same substitution gives loss
exp(-(1/(2b)+o(1))D2). The conventional common-base quota requires
u>=b+1/(2b), while the charged sparse matrix costs 2b. AM–GM gives
b+1/(2b)>=sqrt(2), with equality at b=1/sqrt(2), where 2b also equals
sqrt(2). Both endpoints b->0 and b->infinity diverge. This verifies the
global relaxed infimum in (4.11). Replacing t by eta*t, eta>=1, gives
sqrt(2eta), not an improvement.

For the negative sign the identity q=a^2-ell_i N b^2 remains correct and
cancellation becomes possible. Setting ell=1,b=1 gives the ordinary QS
polynomial (ell=1 here is a comparator, not one of the generated primes).
Negative norms need signs, zeros need exclusion, and changed multiplier/b
families need their own supply and processing analysis. The primary QS
comparison suffices to reject a claim of a new relation architecture; it does
not prove every such variant attains the classical QS constant.

## 10. Exact localized repairs and Section 5's valid scope

These patches belong in a coordinator-edited successor, preserving the
submitted draft. I have not edited the proposer report, intake, registry,
STATE, shared code or Lean.

**P1 — attempted indices, lines 97–119 and 353–398.** Add after the family
definition, and use its notation in the two processor bounds:

> Distinguish the attempted contiguous index pool 0<=i<J from the retained
> subset I, |I|=K. If validation scans Q consecutive candidates, J=Q;
> validation and all failures cost Q poly(n,log J). Retain each original
> index. Heights obey H(f_i)<=(J+1)m+J. The literal index sieve costs
> (M B_A+M J)poly(n,log J), including positions later discarded. The
> H016 stream may enumerate only the retained indexed fields and costs
> (B_A+M K)poly(n,log J) after validation. Any norms processed before
> later rejection count in the actual stream. When J=Q=K at the level of
> L exponents, the displayed leading comparisons are unchanged; no such
> field-yield assertion is proved here.

For arbitrary nonconsecutive attempted indices, J must bound their magnitude
and scan span separately from their count Q. The minimal construction above
uses consecutive attempts; no new search implementation is being proposed.
The same J replaces the family-index K in generic height statements such
as (3.5). Also make the already needed epsilon,delta>0 explicit at line 83.

**P2 — rejected records and widths, lines 707–724, especially (5.1).**
Replace `T_dedup/filter(R)` by `T_dedup/filter(S_pre,U_pre,I_pre;R)`, where
S_pre counts every record submitted to those stages and U_pre,I_pre are
their scalar/payload bit masses. Add:

> Rejected duplicates and unusable rows count in S_pre, even when R=0.
> Norms of every processed failed field count in U. If a norm is avoided
> by an earlier filter, charge that filter's inputs and work separately.
> Deduplication sorts or indexes the records it receives, not merely the
> final survivors. Subsequent lifting charges the actual retained records
> and all maps needed to return to their source equations.

The original prose repeatedly intends to pay these costs; the displayed
function of final R alone is insufficient as a general bound. Under these
cards' polynomial-width explicit streams, sorting all prefiltered records is
still covered by their total stream size times polynomial logarithmic factors.
It cannot improve the constants. State the polynomial-scalar-width condition
explicitly when simplifying Card B's reconstruction cost at lines 645–649.

**P3 — expected supply and expected full cost, lines 726–756.** Retain the
algebra of (5.2)–(5.3), but append these precise sufficient model definitions:

> Let A_N be the number of distinct paid Stage-2 attempts under the actual
> field/pair selection and stopping strategy, and R_N its newly credited
> distinct admissible rows after all stated filters. For the necessary
> expected-quota calculation assume, uniformly in N,
>
>     E A_N <= exp((kappa+2epsilon-tau_R+o(1))D),
>     E R_N <= exp((-tau_A-ell+o(1))D) E A_N,
>     E R_N >= exp((q-o(1))D).
>
> The second inequality is an additional law for this strategy, not an
> average smoothness fact or a consequence of upper norm bounds. A sufficient
> adaptive version bounds the conditional expected newly credited output
> before every paid attempt, given its selection history, by the same rate.
> Nonnegative summation then gives the aggregate law, including stopping.
> For random K or M, bound the aggregate A_N directly, not a product of
> expectations. Count at most one new row per distinct attempt.
>
> To use (5.3) as a sufficient expected-cost envelope, separately establish
> E T_trial<=exp((c_trial+o(1))D), where c_trial is its displayed maximum.
> In particular justify the sparse-matrix/lifting cost by pathwise caps or
> a bound on E[D_mat W], not just E[D_mat] and E[W]. Cap/price excess
> collection, discarded rows, failures, root widths and unsuccessful linear
> algebra. The expected quota alone does not give this cost or a nonzero
> probability of meeting a usable quota.

Taking logarithms of the three supply inequalities yields exactly
kappa+2epsilon-tau_R-tau_A-ell>=q. This is a necessary condition of that
expected-quota model. A different successful mechanism may use fewer rows,
compressed maps or a different law; it is outside that obligation.

For completeness, restart the entire trial with iid randomness and finite
E T_trial, with actual success probability sigma_N>0. The renewal identity

    E T_total = E T_trial + (1-sigma_N) E T_total

gives E T_total=E T_trial/sigma_N even if a trial's cost and success are
correlated. Thus a reciprocal success exponent s adds to c_trial as in (5.3).
Nonidentical/adaptive restarts need a separate conditional bound. Sigma must
include missing quota, failed field roots, denominator failure, trivial gcds
and all other ways a trial fails to return a proper factor. Merely satisfying
(5.2) does not bound sigma. If many dependencies are tried inside a trial,
their costs belong in that trial rather than being omitted through a restart
convention.

These are accounting/quantifier completions of the proposed ledger, not a
proof that its laws hold for actual NFS values. In particular H022 supplies
the lesson about quantifiers, not a transferable many-field yield theorem.
H023's geometry exceptions remain available counterexamples to overbroad
geometry claims; none supplies the missing arbitrary-input field family here.

## 11. Disposition and narrow handoff

The mathematical core passes: known balanced-model reconstruction, global
optimization, progression arithmetic, field-label obstruction, primorial
input-width penalty, and the positive quadratic integer square map. No
incorrect core proof or materially false primary-source attribution was found.
The identified localized full-cost/quantifier gaps require P1–P3; they do not
open a new survivor or invalidate the conditional closures.

**Card A:** close the change confined to processing the same explicit streams
with the same balanced collection/scan/matrix model. **Card B:** retain its
exact maps and counterexample, but close the proposed new factoring advantage
for the explicit constructions and their stated size/yield models. Other
representations, samplers and compatible maps have not been ruled out.

The next action is coordinator adoption/checking of the three local repairs,
not a new experiment or a wider search by this reviewer. No further empirical
question is warranted for these exact cards. Reopening needs a supplied,
materially changed construction with an exact reconstruction map and paid
usable-supply claim; this review selects no such construction and makes no
blanket novelty claim.

Only H028-independent-review.md and adjacent H028-review-* artifacts were
written. Source retrieval/extraction, file copying and hashing are evidence
operations; no finite mathematical experiment, parameter sweep, benchmark,
solver execution, package installation, shared-code/Lean edit, commit,
publication, scheduler or delegation occurred. Project tests were not run for
this document-only symbolic review. The completion manifest is
[H028-review-provenance.json](H028-review-provenance.json).

**Verified full factoring complexity improvement remains NONE.**
