# H026 — Independent symbolic review of base-smooth residual supply

2026-10-08. **ACCEPT equations (1)–(10) and the negative answer to H024's
precisely stated supply question, within the fixed base, aligned weights and
cutoff. No mathematical correction is required.** Two recommended wording
clarifications appear in item 10. They do not change the accepted theorem.
Verified full factoring complexity improvement: **NONE**.

The reviewed parent draft has SHA256
`2d0124e0b7fc46eb2e3e9d22c3520149272882a1b97f4289ff161b251e8a920f`,
matching the task's supplied hash. Its exact bytes are preserved in
[H026-review-submitted-draft.md](H026-review-submitted-draft.md).
The H026 hypothesis has SHA256
`ff4f5cb565c6e38005a7586175ac1cecb4135b3478338b45a073d25ef429edea`.

I read the full H026 hypothesis and report, AGENTS.md, README.md,
docs/SPECIFICATION.md, RESEARCH_LOOP.md, RESEARCH_TEAM.md and research/STATE.md.
I also read the H021/H024/H025 dispositions, relevant H021 construction and
review sections, and the full current H024/H025 reports and independent
reviews. In particular, H024 review item 7 supplies the exact question being
answered. H025's earlier conditional dependency is resolved by H024's accepted
disposition; its corrected power-saving wording is preserved. H023's separate
special-form review was not reopened or duplicated.

All mathematical checks below are symbolic. Reading, source retrieval,
document copying, PDF page rendering/inspection, hashing and report authoring
were the only operations. No research executable, finite experiment, sample,
benchmark, parameter sweep, package, Lean change, recursive delegation, commit,
publication or scheduler was used. Only this review and adjacent
`H026-review-*` artifacts were written. The parent report/hypothesis, STATE,
registries, shared code, Lean and old evidence were not edited.

**1. Dependency interface and common universe — ACCEPT.**

Write ln for the natural logarithm. The accepted construction fixes

    ell = bit_length(N) >= 2, k = ell,
    p_j = the j-th prime, f_j = ceil(j/2),
    C = the least power of ten at least ell,
    a_j = round_star_C(p_j), T = round_star_C(N),
    F_N(e) = q(e) + (sum_j a_j e_j - T)^2,
    q(e) = sum_j f_j^2 e_j^2.

H021's round_star is the accepted exact rational, bounded-error rule. It is
not literal nearest rounding of a true logarithm. H024 uses

    r = floor((2T+a_1)/(2a_1)),
    e_star = (r,0,...,0),
    E_star(N) = r^2 + (a_1 r-T)^2,  0 < E_star(N) < 40ell^2.

Thus e_star belongs to S_N, so S_N is nonempty. Since F_N(e)>=q(e), every
S_N is contained in the same finite U_ell={q(e)<=40ell^2}. Positivity of
the weights bounds each coordinate and proves finiteness. The log target and
the actual cutoff may depend on N; the containing universe depends only on
ell. The pairing of the increasing primes with these particular weights is
part of its definition.

The accepted H024 count is for the diagonal universe itself, for every finite
k and E>=1, and therefore applies at E=40ell^2:

    |U_ell| <= exp(11(40ell^2)^(1/3))
            = exp(K ell^(2/3)), K=11*40^(1/3).

This does not substitute an N-dependent F-population bound into a union over
N. No DP implementation, enumeration runtime, sampling distribution or
optimizer-recovery assertion is needed. H021's corrected recovery restriction
remains unchanged. H025 supplies the fixed-universe viewpoint; its small-window
density conclusion is not being used as a smoothness premise.

**2. Width over every element of U_ell, equations (2)–(3) — ACCEPT.**

The accepted prime bound is p_j<=4(j+1)^2 for every j>=1. Since j+1>=2,

    ln p_j <= ln 4 + 2 ln(j+1) <= 4 ln(j+1).

Combining this with f_j>=j/2 gives the factor 64 in equation (2). For the
dyadic block 2^r<=j<2^(r+1), there are 2^r indices, j^2>=2^(2r), and
ln(j+1)<=(r+1)ln 2. Hence its contribution is at most
(r+1)^2(ln 2)^2/2^r. Differentiating the convergent geometric series gives
sum_{r>=0}(r+1)^2/2^r=12. Consequently

    sum_{j>=1}(ln p_j/f_j)^2
      <= 64*12*(ln 2)^2 < 768.

Cauchy–Schwarz now applies to every e in U_ell, without requiring its log-row
constraint:

    sum_j |e_j| ln p_j
      <= sqrt(q(e)) * sqrt(sum_j (ln p_j/f_j)^2)
      < sqrt(40*768) ell < 176ell.

The last strict inequality follows from 176^2=30976>30720=40*768. Positive
and negative exponent parts are each bounded by the entire nonnegative sum,
so ln u_e, ln v_e<176ell. Products with an empty exponent support equal one.
For ell-bit N, ln N<ell ln 2<ell. Since u_e,Nv_e are positive,

    |u_e-Nv_e| <= max(u_e,Nv_e) < exp(177ell)=X_ell.

This avoids a needless factor two and includes residual zero. Bounding the
larger Cartesian coordinate box instead of U_ell would not justify this
sharper estimate; the draft correctly uses the diagonal energy constraint.
There is no lower bound on residual size in this step.

**3. Finite Euler product and subexponential smooth-value count,
equations (4)–(6) — ACCEPT.**

Let P_ell(X) be the set of positive integers at most X supported on the first
ell primes, including one. For sigma>0, each n in this set contributes at
least one to X^sigma n^(-sigma). Unique prime factorization and a finite
product of convergent nonnegative geometric series therefore give

    |P_ell(X)| <= X^sigma sum_{supported n>=1} n^(-sigma)
               = X^sigma product_{j<=ell}(1-p_j^(-sigma))^(-1).

Convergence needs only sigma>0 because the prime set is finite. No claim
about independent divisibility events, random residuals, an infinite Euler
product or a Dickman approximation occurs here. Real, noninteger X is harmless.

For sufficiently large ell, sigma=2 ln ln ell/ln ell lies in (0,1]. Put
m=floor(sqrt(ell)). For j<=m, monotonicity in p_j and p_j>=2 give

    -ln(1-p_j^(-sigma)) <= -ln(1-2^(-sigma))
                          <= ln(2/(sigma ln 2)).

Indeed, for 0<=y<=1, the exponential remainder bound gives
1-exp(-y)>=y-y^2/2>=y/2; take y=sigma ln 2. There are at most sqrt(ell)
such terms. For j>m, the integer j is greater than sqrt(ell), and the
elementary bound p_j>=j+1 implies

    p_j^(-sigma) <= exp(-sigma ln ell/2) = 1/ln ell.

Eventually 1/ln ell<=1/2. Integrating (1-z)^(-1)<=2 on [0,1/2] proves
-ln(1-z)<=2z. Summing at most ell remaining terms gives 2ell/ln ell.
The X_ell^sigma contribution is exactly
177ell*sigma=354ell ln ln ell/ln ell. Thus define

    L_ell = 354ell ln ln ell/ln ell + 2ell/ln ell
            + sqrt(ell) ln(2/(sigma ln 2)).

The draft proves ln Psi_ell(X_ell)<=L_ell. Its last logarithm equals

    ln ln ell - ln ln ln ell - ln ln 2,

and is O(ln ln ell) eventually. Dividing all three terms of L_ell by ell
shows L_ell=o(ell); in fact L_ell=O(ell ln ln ell/ln ell). Floor handling,
signs and the coefficient 354 are correct. Small ell are outside this
asymptotic substitution, but the finite product remains valid for every
sigma>0. No useful finite bit-length threshold is established.

**4. Counting inputs from vector/residual pairs, equations (7)–(8) — ACCEPT.**

For fixed ell and e, both u_e and v_e are fixed positive integers, and v_e
is never zero. Given a signed integer w, the equation
N=(u_e-w)/v_e has at most one integer solution in the ell-bit interval.
The eligible signed residual set is

    {0} union P_ell(X_ell) union (-P_ell(X_ell)),

with cardinality 2Psi_ell(X_ell)+1. Including values at the upper endpoint
X_ell is a safe enlargement of the strict residual bound. Both signs of
one are included. Zero is a separate value and is not called smooth.

Every qualifying input has at least one pair in this common finite set.
Discard pairs producing a noninteger N or an N outside the interval, then
project the remaining pairs to their N. The projection is surjective onto
the qualifying inputs, so their number is no larger than the pair count.
It need not be injective. Multiple representations and correlations cannot
increase this upper bound.

For an explicit common error term, set

    D_ell = K ell^(2/3) + L_ell + ln 3 = o(ell).

Since Psi_ell(X_ell)>=1, one has 2Psi+1<=3Psi. Thus for all sufficiently
large ell the number A_ell in the draft satisfies

    A_ell <= exp(D_ell).

This verifies the stated exp(O(ell^(2/3)+ell ln ln ell/ln ell)) bound.
No algorithm to list, recognize or select these pairs is asserted or needed.
Paying selector cost cannot strengthen a pointwise existence event beyond
the union already counted. Arbitrary optimization or randomization within
S_N, including an unlimited selector, remains covered by S_N subseteq U_ell.

Zero introduces no loophole after small-prime removal: the positive and
negative exponent products are coprime. If u_e=Nv_e, then v_e divides u_e,
forcing v_e=1 and N=u_e supported on the base. Such N>1 cannot be coprime
to the primorial. Counting zero anyway is a valid stronger ambient bound.

**5. Uniform ell-bit density, equation (9) — ACCEPT as an upper bound.**

The interval I_ell={2^(ell-1),...,2^ell-1} has exactly 2^(ell-1) integers.
Hence the probability of even the larger U_ell event under its uniform law
is at most

    min(1, 2 exp(D_ell-(ln 2)ell)).

The draft's exp(-(ln 2)ell+o(ell)) upper rate follows, with the constant
factor two absorbed in o(ell). This is not an asymptotic equality for the
actual event probability. It is also not a probability law for a particular
fixed input or an arbitrary conditioned input distribution.

For every input outside that exceptional set, S_N has zero nonzero
base-smooth residuals and remains nonempty. Thus the conclusion is stronger
than merely saying that a uniform draw from S_N rarely succeeds on those
inputs. It still leaves all behavior on exceptional inputs unconstrained.

**6. New primary quantitative premises — ACCEPT after direct verification.**

I independently opened Rosser and Schoenfeld's *Approximate formulas for some
functions of prime numbers* and visually inspected printed page 69, PDF page
6 (zero-based index 5), including its labels and inequality restrictions.
Corollary 1 gives precisely

    (3.5) y/ln y < pi(y),                 y >= 17;
    (3.6) pi(y) < 1.25506 y/ln y,         y > 1.

Both inequalities are strict, and the lower-bound endpoint includes 17.
The paper defines pi(y) by counting primes at most y and uses real y. These
are unconditional inequalities, not estimates restricted to integer y or
conjectural prime-density assumptions. The primary source is the
[Rosser–Schoenfeld 1962 paper](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf).

The independently retrieved PDF is preserved as
[H026-review-Rosser-Schoenfeld-1962.pdf](H026-review-Rosser-Schoenfeld-1962.pdf),
SHA256 `8e37b06f82e09421bceb2502578c47b61469141f0287e6acedb70e01765ab556`.
The adjacent rendered p. 69 image records the inspected page. I verified the
quoted premises against the primary scan; I did not reprove that paper's
analytic number theory. These two bounds are the only new external
quantitative premises. The earlier prime upper bound is already accepted
through H021, whose cited inequality (3.13) is also visible on this page.

**7. Balanced squarefree semiprime denominator, equation (10) — ACCEPT.**

Let x=2^((ell-1)/2), a=sqrt(2)x, and R_ell count primes in (x,a). Since
pi(a)-pi(x) counts x<p<=a, removing a possible prime upper endpoint gives

    R_ell = pi(a)-pi(x)-1_{a is prime}
          >= pi(a)-pi(x)-1.

There is no further subtraction for the lower endpoint: pi(x) already
removes it. For sufficiently large ell, a>=17 and x>1, so the primary
inequalities apply at the required arguments and yield

    R_ell > (x/ln x)
             [sqrt(2) ln x/(ln x + (ln 2)/2) - 1.25506] - 1.

Let delta=sqrt(2)-1.25506>0. Its positivity needs no numerical experiment:
1.25506<4/3<sqrt(2). The bracket tends to delta. It is eventually at least
delta/2, and x/ln x tends to infinity, so the subtractive one can be absorbed
to obtain R_ell>=(delta/4)x/ln x eventually. This is a bound for every
sufficiently large integer ell, not just a subsequence or an average over
bit lengths.

Each distinct pair p<q in this open interval satisfies

    2^(ell-1)=x^2 < pq < 2x^2=2^ell,
    1 < q/p < sqrt(2).

The product is squarefree with exactly two prime factors. By unique
factorization, distinct unordered pairs yield distinct products. Therefore
the stated ensemble has exactly binom(R_ell,2) elements. Eventually R_ell>=2
and binom(R_ell,2)>=R_ell^2/4; using x^2=2^(ell-1) and
ln x=((ell-1)/2)ln 2 gives

    |B_ell| >= c_B 2^ell/ell^2

for an absolute c_B>0 and all sufficiently large ell. This proves (10).
Exponential x eventually exceeds 4(ell+1)^2>=p_ell, so both prime factors
are outside the entire generator base. Every product in B_ell is then
coprime to that base. No H023 family claim or semiprime distribution
heuristic enters this comparison.

**8. Restricted density and rejection of the named universal lemma — ACCEPT.**

The count of qualifying members of B_ell is at most A_ell, even if every
ambient exception were concentrated there. Consequently

    #{N in B_ell : some e in S_N has nonzero base-smooth w_N(e)} / |B_ell|
      <= min(1, c_B^(-1) ell^2 exp(D_ell-(ln 2)ell))
      <= exp(-(ln 2)ell+o(ell))

eventually. The polynomial denominator loss contributes only 2 ln ell+O(1)
to the exponent. This supplies exactly the restricted-set normalization
that H025 deliberately did not assume.

The upper bound tends to zero. For every sufficiently large ell, B_ell is
nonempty and contains inputs with no such residual; the fraction of these
inputs tends to one. They are composites coprime to the base and have
nonempty S_N. On each of them the requested fraction is exactly zero,
contradicting ell^(-A)>0 for every fixed A>0. Arbitrarily large such N exist,
so no choice of a finite all-input starting threshold rescues the lemma.

This is an unconditional mathematical falsification of H024 review item 7
for its exact generator, after importing the accepted dependencies and the
verified primary inequalities. It does not assert that every semiprime in
B_ell fails, nor identify a failing semiprime without first performing some
additional computation. It makes no efficient counterexample-construction
claim and no useful practical threshold claim.

**9. Material boundaries — ACCEPT the restrictions; REJECT stronger readings.**

Aligned weights are used in the width argument, not just in the population
bound. A permutation preserves the diagonal count but can destroy uniform
O(ell) output width. As a purely symbolic scope check, for ell>=3 swap the
weights at indices 2 and ell, retaining f_1=1. The ell-th prime then has
weight one. Taking e_ell=6ell and every other exponent zero has diagonal
energy 36ell^2<=40ell^2, yet

    ln u = 6ell ln p_ell >= 6ell ln(ell+1).

Thus O(ell) width does not hold over that permuted diagonal universe, even
though its population count and the first-coordinate feasible cutoff survive.
This is a counterexample to transferring this proof step, not a claim that
the permuted generator supplies useful residuals. No permutation extension
is accepted.

The smoothness base must also remain the first ell primes. Polynomial size
alone does not supply this proof's o(ell) smooth-value exponent: replacing
ell by another number of primes changes the product, its split and its tail
sum. A larger base may invalidate that conclusion. Larger energy changes
both the population and width envelopes. Neither modification is asserted
to succeed or fail by the present theorem.

N-dependent bases or weight assignments require a controlled union of fixed
pairs. The draft's final union-bound remark is valid only with uniform
exceptional-count bounds: if J_ell versions each have at most exp(d_ell)
exceptional inputs, where d_ell=o(ell) uniformly and ln J_ell=o(ell), their
union has at most exp(d_ell+ln J_ell)=exp(o(ell)) inputs. Separate pointwise
asymptotics for versions that change with ell are insufficient. This formal
union calculation neither constructs such versions nor accepts any changed
base, weight, energy or adaptive algorithm. Those require further review.

The result concerns H021's original exponent-coordinate objective and H024's
cutoff. There is no established containment of the paper's post-LLL correction
domain or perturbed tensor-network sampler in this universe. Their behavior,
all logarithm-lattice algorithms, other branches of a factoring algorithm,
exceptional inputs and factoring generally remain outside the conclusion.
No useful factor algorithm, factoring hardness theorem, general lower bound,
relation-rank guarantee or proper square-root split follows.

**10. Concrete wording clarifications and final disposition.**

No equation or proof needs repair. For scope clarity, I recommend adding
this sentence to the parent's final section:

> The O(ell) width bound uses the specified alignment f_j=ceil(j/2) with the
> j-th prime; preserving the multiset of weights under a permutation is not
> sufficient to preserve that bound.

I also recommend replacing “It removes the hypothetical randomness law used
only conditionally in H024” with:

> This input-density obstruction needs no hypothetical randomness law. It
> does not establish H024's conditional per-attempt rarity law for every
> fixed input or adaptive history, and exceptional inputs remain possible.

These clarify already scoped claims. The proposed deterministic theorem is
accepted as written; the universal density lemma it targets is rejected.
No extension to other generators is approved, and no further experiment or
implementation is needed for this review. The coordinator can record the
scoped result and the optional clarifications without changing old evidence.
Verified full factoring complexity improvement remains **NONE**.

Exact dependency, governing-file and archived-source SHA256 identities are in
[H026-review-inputs.sha256](H026-review-inputs.sha256). The manifest records
the accepted current H024/H025 reports as well as their original submitted
snapshots, so the previously repaired wording is not confused with the
present mathematical dependencies. STATE changed concurrently under coordinator
ownership: its first recorded hash was
`d49cf52b4d81f5988be5336d8e34b7eb0f36049074eafd316a5b0e3265ca2c82`,
and the closing manifest records
`7c3faa43d8bce57722e67b712507056e0687dd452b7f6cc1339e5200d62b841a`.
The updated H026 checkpoint was also inspected. STATE is not a mathematical
premise of this proof, and these identities do not require freezing it.
