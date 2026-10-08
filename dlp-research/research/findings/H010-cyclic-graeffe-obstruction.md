# H010: first-block obstruction for the frozen cyclic Graeffe schedule

Verdict: independently checked paper rejection of the frozen elementary sparse
schedule and its proposed Theta(B)-row collector. No Lean proof, numerical
experiment, new attack, or general coordinate-method lower bound. Improvement
versus the accepted classical reference remains NONE.

## Operation and assumptions

The original operation is retained in ../hypotheses/H010-cyclic-graeffe-v1.md.
Ordinary short-Weierstrass E/F_p has full prime order q, p~q~B^5. Five domains
B_i~B are powers of the distinct primes 2,3,5,7,11, N=product B_i divides p-1.
Parameters are supplied correctly for this argument; efficient growing-family
construction remains unproved and would be charged. Shifts u_i are fixed before
fresh uniform targets R. Let r=x(R), e_i=N/B_i, and

    A_r(Z)=S6(u1+Z1,...,u5+Z5,r),  f_r(T)=A_r(T^e1,...,T^e5).

The frozen algorithm stores canonical sparse coefficient maps, processes all
factor-2 stages first, and explicitly visits every input term pair when forming
g_j(X)*g_j(-X) modulo X^(N/2^j)-1. It emits at most one verified relation only
after the norm and root-descent schedule. Earlier output using a different
relation-search operation is not this frozen algorithm.

## Exact norm and support argument

Put b0=min B_i>=64. Choose a=2^t as the largest power of two <=b0/32. Then
b0/64<a<=b0/32, a divides B1, and a further factor-2 stage remains. Require
p>16a, automatic eventually in the proposed scaling.

After t stages the cumulative norm is the canonical cyclic reduction of

    F_a(Z)=product_(xi in mu_a) A_r(xi*Z1,Z2,Z3,Z4,Z5).

To see this, a divides e_i for i>1 while gcd(a,e1)=1. The a original T-rotations
therefore fix the last four coordinates and permute all rotations of the first.
Multiplication/reduction at intermediate stages preserves this identity in the
quotient. Invariance in Z1 shows F_a=J_a(Z1^a,Z2,Z3,Z4,Z5), with degrees

    deg_1 J_a <=16;  deg_i J_a <=16a for i>1.

Set n=N/a, C1=B1/a and C_i=B_i for i>1. Under Y=T^a the monomial map is

    nu |-> e1*nu1 + sum_(i>1) (e_i/a)*nu_i
        = sum_i (n/C_i)*nu_i   modulo n.

The C_i are pairwise coprime, 16<C1 and 16a<B_i. Reducing any equality of
these weighted exponents modulo C_i and using gcd(n/C_i,C_i)=1 proves that
the map is injective on the ENTIRE degree box. Thus cyclic reduction cannot
cancel the selected face against any other monomial. This argument allows
ordinary univariate exponents greater than n; it does not confuse degree with
support and does not reuse H009's quotient-series argument.

Use the standard Semaev normalization and leading-coefficient identity
LC_x S_m=S_(m-1)^2, together with LC_x S3(x,y,r)=(y-r)^2. Successive extraction
in variables 1,3,4,5 (each exponent16) gives

    [Z1^16 Z3^16 Z4^16 Z5^16] A_r = (u2+Z2-r)^16.

Indeed the powers after successive extractions are S5^2, S4^4, S3^8 and the
sixteenth power of the remaining coordinate difference. Shifts do not change
these leading coefficients. In the product of a factors, the top exponent in
each selected variable requires the top exponent from every factor. Therefore

    [W1^16 Z3^(16a) Z4^(16a) Z5^(16a)] J_a(W1,Z2,...,Z5)
      = (u2+Z2-r)^(16a).

The aggregate phase is (product xi)^16=1, including even a. For r!=u2 and
p>16a, all 16a+1 binomial coefficients and powers of u2-r are nonzero. Full-box
injectivity preserves these distinct coefficients in g_t. Consequently

    support(g_t) >=16a+1 >b0/4.

The NEXT prescribed factor-2 convolution multiplies g_t(X) by g_t(-X). Its
input supports have equal size, so it visits at least

    L=(16a+1)^2 > b0^2/16 = Omega(B^2)

term pairs, even if many output coefficients cancel. This is a literal operation
count, not an Omega(B^2) memory claim. Input storage at this stage is Omega(B)
records. It does not constrain FFT multiplication, compressed representations,
or a changed schedule.

## Caps, failures and full collector cost

For uniform finite R, the exception r=u2 has probability eps<=2/(q-1), since an
x-coordinate has at most two rational points. Let X be paid work per attempted
query and Y in {0,1} its emitted verified-row count. Every attempted query costs
at least one event. A nonexceptional emitted row requires X>=L. Hence

    E Y <= E X/L + eps <= (1/L+eps) E X,
    E X >= gamma E Y,  gamma=1/(1/L+eps)=Omega(B^2).

This remains valid with early abandonment and arbitrary caps: unfinished queries
need not consume the whole cap. It does require fresh uniform sampling and the
frozen rule that a normal successful output goes through the prescribed stage.
Treating infinity as a further exceptional uniformly sampled group point gives
eps<=3/q and the same conclusion. Sampling costs are never free.

Condition on the preceding history before each predictably attempted query.
With fixed shifts and fresh uniform targets the same inequality holds. Sum over
finite prefixes, then use nonnegative monotone limits for stopped collectors.
If the proposed collector needs Theta(B) emitted usable rows and completes with
constant probability, expected work is Omega(B^3), above the B^(5/2) reference
up to polylogarithmic arithmetic factors. Counting only independent rows cannot
increase Y. Rank failures, extraction, signs and final verification add cost.

This does NOT prove all ECDLP algorithms need Theta(B) rows. Nonuniform target
selection, useful early dependencies, batched outputs, changed multiplication
representations or another transform order require new algorithms and ledgers.
Construction, factor-base setup and family generation remain charged additions;
optimistic zero construction cost would not rescue this particular collector.

## Independent review and process

- Proposer: native Astra /root/h006_structured_relation_ideas, concrete cyclic
  schedule with root-index descent; cost unproved when proposed.
- Operational obstruction: native Sol /root/h010_early_dependencies, new distinct
  review after its completed early-dependency cards. Read-only, no experiments.
- Independent adversarial verification: native Astra /root/h007_additive_relations
  checked cumulative norm, phase, entire-box CRT injectivity, exact face and
  cap-independent work/reward inequality. Root independently repeated these
  derivations. All three distinguish this from H009 literal division.
- Claude Opus5.5 independent primary-literature/family review COMPLETED:
  node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h010-graeffe-priorart-opus-20261008-r1.
  Raw report and root qualification are retained separately. It does not
  independently verify this new obstruction; native review does.

The correctness review also requires gamma generated from F_p^* (or explicit
order-N membership check), and COMPLETE zero-divisor columns/degree accounting
for the separate split-fiber conditional cancellation argument. These corrections
are retained in the hypothesis card; no unqualified common-composite exclusion.

The standard Semaev identities and prior-art context were already checked in
H009, with [Gorla–Massierer](https://arxiv.org/pdf/1403.0126) as a primary source.
[Deterministic Graeffe root finding](https://www.texmacs.org/joris/dmodroots/dmodroots-abs.html)
and [randomized tangent Graeffe](https://www.texmacs.org/joris/rmodroots/rmodroots.html)
are established methods, not discoveries here. Their results do not supply the
missing complete-cost bound for this ECDLP collector. Root opened both sources
this wave; the latter assumes split separable input and excludes some public
setup costs. The mathematical rejection above is a derivation, not a theorem
attributed to these papers.

Validation command: `./scripts/check.sh > /tmp/ecdlp-h010-graeffe-check.log 2>&1`
passed exit0 with 363 existing theorem audits. No Lean code or Audit entry changed.
No ECDLP numerical run, parameter census, implementation, or new proof infrastructure
was needed. Next: integrate remaining independent adaptive-sampling/hybrid ideas
and source review; require a changed concrete operation before reopening this
schedule. No validated improvement or practical throughput result.
