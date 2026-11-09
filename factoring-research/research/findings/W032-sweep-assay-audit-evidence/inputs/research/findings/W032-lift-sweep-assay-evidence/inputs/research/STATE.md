# Factoring research checkpoint

Updated: 2026-10-08.

- User focus: **factoring experiments + focused Lean specifications**.
- User authorizes ongoing algorithm research and T3 child agents.
- Research goal: **ACTIVE**. No pause or completion has been requested.
- Verified new algorithmic complexity improvement: **NONE**.
- Environment: complete; Python diagnostics and pinned Lean checks run.
- Best formally checked result: correctness of the exhaustive reference splitter.
  The polynomial-time goals are specifications relative to an abstract machine,
  not existence proofs.
- No recurring schedule, publication, or commits are authorized by this loop.

## Resume here

**User operating-mode change, 2026-10-08:** the parent actively develops new
computational mechanisms; T3 children audit, check prior art, seek counterexamples
and run only preregistered bounded tests. Pending review blocks acceptance of
that claim, not independent brainstorming. Avoid status/wait turns when useful
constructive work exists. Keep a small diverse shortlist and measure progress by
saved computation and resolved bottlenecks.

The parent has two active constructive branches. [W032](hypotheses/W032.md)
evaluates one scalar
in a quadratic algebra at precision N^(2R+3), normalize by an exact N^2
division and a unit, then test its canonical higher base-N digits. This
replaces the W031 coefficient grid by O(log N) pair-powering stages on
O(R log N)-bit residues. Acquisition is explicit; a separating probability
or deterministic cover is NOT established. Verified complete improvement NONE.

The [scalar and affine-lift audits are now accepted](findings/W032-symbolic-parent-disposition.md).
Both reports were read in full, including the exact symbolic source/output;
all 17 scalar and 15 lift payloads match their external terminal anchors.
The scalar diagonal now satisfies the lift audit's provisional dependency.
The parent derived [an exact floor representation](findings/W032-canonical-floor-structure.md)
using D=4^R(2R+1)! and integer polynomial F. The top digit is
floor(F/(D N^(2R))+hN/D) mod N, where hN^(2R+1)=-F mod D. At R=3 this
includes a nonconstant quartic/N^2 carry, so a degree-six field-root bound
does not directly apply. The first digit is a unit and the second has a
quartic formula on residue classes modulo 24. Those identities passed their
independent audit, with no complete factoring guarantee. The review supplies
an exact d3 formula with one nonconstant integer floor, recorded in the parent
disposition. For fixed R the same screen needs only public polynomial/floor
arithmetic; growing R still favors the scalar acquisition over a naive table.

A further [input-lift calculation](findings/W032-lift-control.md) gives
d_R(a0+N^(2R-2)t)=d_R(a0)+(a0/12)t mod N for R>=2 on the checked-unit
branch. The coefficient is invertible. This shares one scalar power across
the lifted family, but uniform t gives exactly a uniform gcd argument;
forcing zero gives full gcd N. Its scoped audit passed. Preserve the acquired
base's information/cost and adaptive/batch consumption: the affine simulation
does not show those are useless or lower-bound their algorithms. It does not
settle the original canonical-input interval's distribution.

The [ONE frozen assay is accepted at finite scope](findings/W032-assay-parent-disposition.md):
155/155 cases, 131 units, all required identities and five matrix controls
passed, 19,964/20,000 events and 0.264330 seconds rounded up. No stopped,
failed or unstarted case. All six Python sources and full protocol/report
were read; all 31 delivery and 19 freeze payloads match; stored ledgers agree.
No numerical rerun. Later digits split 28 N=143 unit inputs missed by d2;
this is not a scaling or success-law claim. scripts/check.sh passed all
12 Python tests, source screen, pinned Lean build and axiom audit after
the standalone code was present. These checks are not proofs of W032.

The [joint-lift, high-difference, near-top and exact-period results are now
accepted at their scoped levels](findings/W032-W033-parent-disposition.md).
All five reports in that intake, including the W033 cover report, were read
in full; all externally anchored payloads match. No new numerical run.
Full-lift randomization gives independent uniform high digits for a digit-only
consumer. The D-spaced order-2R+1 filter leaves |c|<4^R and cannot split
large-factor inputs under its factorial-width guard. The order-2R-1 filter
retains A*u+c, |c|<4^(R-1), but uniform-start success is at most p^(-1+o(1))
on the stated comfortably-wide large-factor semiprime families. Globally
small linear-signal targeting also fails at its stated small-residue gate.
Neither bound applies to all selectors, individual digits, or arbitrary
consumers. Carry correlation is one possible future route, not a proved
necessity. No complete factoring gain follows.

The parent supplied an actual [exact carry-label period algorithm](findings/W032-exact-label-period.md).
It strips known prime factors of D after testing function equality through
integer-valued polynomial differences; it does not enumerate D inputs.
The independent audit accepts polynomial(R,bitlen(N)) acquisition and the
new width guard (2R+1)*S_min<N, and proves exactly
v_2(S_min)=v_2(D)-1-v_2(R). Its full odd-prime growth remains unresolved.
The parent's later [period lower bound](findings/W032-label-period-lower-bound.md)
forces every prime R+1<ell<=2R-3 as well. Combined with the power of two,
it proposes 4^R<=N^(alpha+o(1)), alpha=log(4)/(4log(2)+1)<1/2, and thus
rules out this period compression for balanced-input amplification. This
NEW proof has its own LIVE audit; do not mark it accepted from the earlier
period-algorithm review or conflate it with a factorial-scale lower bound.

The strongest new constructive computation is the
[unit-step remainder filter](findings/W032-unit-step-remainder-filter.md).
Use a_i=a0+i and multiply the order-2R+1 digit difference by the unit D;
varying h labels vanish modulo N, removing the equal-label width requirement.
Under the explicit guard |epsilon(a_i)|<1, its gcd equals the gcd of an
integer difference of y_i=sigma_i+[P(a_i)-sigma_i]_D, where P is an
explicit lower-degree polynomial built using N inverse modulo D. This
eliminates 2R+2 scalar powers. A conservative table guard
max_(k<R)|C_k(a_i^2)|<N^2-1 certifies both the tail size and its sign without
forming N^(2R). All coefficient/table widths, O(R^3) straightforward integer
operations, failed guards and nonunit exits are paid. A separate LIVE audit
checks these new identities and costs. Its useful separating yield remains
UNPROVED, and no experiment has been preregistered or run for it.

The distinct branch [W033](hypotheses/W033.md) revisits direct divisibility.
The reviewed axis CRT grid fails its acquisition/height goal; its prime-group
coefficients already expose factors after their expensive construction.
The derivative-exclusion consumer is accepted integer-residue machinery
already present in W006, with its general-composite scope proved separately.
He--Sahai's recent one-dimensional obstruction does not refute rank-two covers.
The new [random oblique grid](findings/W033-random-oblique-grid.md) has an
actual cheap N-only slope generator but known consumers pay KH or H^2+K,
retaining a square-root gate. The [primitive-ratio extension](findings/W033-primitive-ratio-sharing.md)
removes repeated rational factors and derives an exact conditional unit-slope
separating law when H^2<p<=q. The support still has Theta(H^2) tags. Raw
sample counts and accepted-unit counts are now explicitly distinguished.
This extension and its full costs have a separate LIVE audit.

Live tasks: W032 period-bound review, W032 unit-step review, and W033
ratio-sharing review. Full handles and briefs are preserved in
[tasks-W032.json](tasks-W032.json) and [tasks-W033.json](tasks-W033.json).
The near-top and exact-period ALGORITHM tasks are completed and intaken.
Do not duplicate them or rerun the frozen W032 scalar assay.

Next principal research: analyze the exact N-dependent remainder polynomial
and its support as R grows, including the conservative guard's viable range.
Try to share multiple starts through an actual polynomial/remainder evaluator,
and compare that cost with the number of distinct useful integer arguments.
Do not treat a large residual bound as a positive root-density theorem.
Keep the oblique-product branch separate; its distinct-ratio normalization
removes multiplicities, not the still-unresolved aggregate evaluation cost.
Continue constructive work without waiting for the three nonoverlapping audits.

The preceding [W031](hypotheses/W031.md) has two concrete
computations developed after the W030 transition-range finding. A joint
quadratic-chart/carry block has a dense footprint b^3*c^2 and X*T/(b*c)
evaluation points. In the transition regime T>=sqrt(X), this particular
implementation cannot avoid visiting the root coordinates. The b=1 boundary
also pays at least X points. This is a priced template, not a lower bound
on all implicit chart consumers.

The independent reversed-circuit route sets J_N(t)=t^((N-1)/2)F_N(1/t).
The proposed identity trace([[2z,-4],[1,0]]^N)=2z*J_N(z^2) computes its
low jet using binary matrix powering in a truncated polynomial ring.
The [initial jet audit is accepted](findings/W031-jet-parent-disposition.md).
The first RAW coefficient gcd that splits is at index (p-1)/2. A separate
valuation proof extends this to all odd composites, returning N/p, without
confusing prime-component degree with behavior modulo prime powers. The
literal jet search still needs order-p coefficients. Modular extraction
uses inverse 2 and an index shift, not integer halving of canonical residues.
All 15 delivery payloads and 10 frozen inputs match, including the external
manifest anchor. The task is terminal in [tasks-W031.json](tasks-W031.json);
no numerical experiment ran.

The parent continued independently with [higher N-adic precision](findings/W031-higher-precision-prime-screen.md).
The universal polynomial A_j(Y)=product_i((2i-1)^2-Y)/(4^j*(2j+1)!) gives
the normalized reversed coefficient at Y=N^2. Successive exact divisions
recover its coefficients c_(j,r) modulo N. This is a real additional
screen: c_(3,1)=-37/46080 can expose factor 37 before the raw onset. A
direct gcd(N,37) implements that particular test more cheaply. The parent
corrected W031's wording: the raw onset is not a theorem excluding every
normalized operation.

For separate gcd tests of this fixed coefficient family, total numerator
log-height is O((R+1)K^2 log K). The proposed coverage count requires at
least square-root-P precision-volume, up to logs, to cover all primes of
scale P using the displayed dense method. The Codex review is completed
in tasks-W031.json, and this result is now
[accepted with repairs](findings/W031-screen-parent-disposition.md).
All 19 payloads and the external terminal manifest anchor match. The staged
37 example needs a 7-unit condition; lower coefficient lifts require higher
precision than modulo N; raw matrix cost is not complete normalization cost.
A direct recurrence supplies the same screen in soft (K+1)(R+1) modular work.
The exact missed-semiprime argument needs two uncovered primes, with uniform
caps across the input interval. This excludes arbitrary input-dependent
combinations and does not bound all algorithms. All W031 tasks are terminal.

This motivates an actual input-dependent combination or
another mechanism that changes this public screen, while paying for its
degree, generation and success rate. Uniform evaluation of a nonzero
degree-d polynomial has at most d/p zero probability at a prime component;
merely naming point selection or implicit valuation is insufficient.
No shared solver or Lean code changed in this continuation. The W032
standalone certificate and symbolic source have been read; required project
checks passed, with the frozen numerical assay kept at one run.

The prior construction [W030](hypotheses/W030.md) acquires two
one-dimensional square-class root tables, then multiply their base-ell
digits WITHOUT propagating carries, discarding terms above the required
precision. This represents every pair root with O((U+V)log Q) input digits
and only O(ell log_ell Q) carry overhead. Balanced setup is on the scale
sqrt(M) rather than emitting M pair roots or M^(4/5) chart arrays.
The exponent is an explicit triangular bilinear form in the two digit
vectors. Low-digit table groups implement W024's nonzero filter without
pair enumeration. The [root audit is now accepted](findings/W030-root-parent-disposition.md)
with explicit setup, valuation, width and frozen-product accounting.
Column preprocessing permits O(L) work for one supplied pair. This is
not a complete factoring gain; the existing product consumer still pays M.
All 17 delivery payloads and 12 frozen inputs matched the manifest, whose
hash also matched its external terminal anchor. No experiment ran.

The parent [digit-cut continuation](findings/W030-digit-cut-consumer.md)
gives an actual recursive consumer: fix low digits, absorb cross terms in
row/column labels, and lower the interaction precision. The terminal
rank-one product is an ordinary monic multipoint operation, but the root
congruences make terminal buckets singleton in the balanced ranges, so
this direct recursion still reaches every pair. Dense-box and explicit
subset alternatives are also priced, without claiming general lower bounds.
All W030 tasks are now terminal and preserved in [tasks-W030.json](tasks-W030.json).
The [digit recursion and frontier reviews are dispositioned](findings/W030-kernel-and-frontier-parent-disposition.md).
The Grok kernel audit followed two Opus provider failures. Both Opus rounds failed
with repeated provider API errors and produced no report; their terminal
handles are preserved. A new explicitly changed-provider Grok round (r3)
completed with the full brief and failure history. Its exact cut and
terminal monic algorithm are accepted with parent corrections: rank-one
bilinear exponents are not multiplicatively separable values; localization
must descend on gcd=N; signed intervals need explicit splitting; and the
dense box, not its logarithm, is superpolynomial in N. All 16 delivery
payloads and 10 frozen inputs match; no external manifest anchor was supplied.

The parent has now derived the [unbalanced cost frontier](findings/W030-unbalanced-cost-frontier.md).
Even granting a consumer U+V+sqrt(UVT), obtaining the long table gives
cost (N/P)^(1/3) for p on the scale P>=N^(2/5). The small-factor product
branch sqrt(P) meets this at exponent 1/5. The balanced 1/6 target is
therefore not a complete bound for the displayed composition. This is a
cost model calculation, not a lower bound on factoring or all root algorithms.

A concrete public repair restricts u=s*a with s~N/P^2 and balanced a,b
tables. Its cover uses radicand N*s while the exponent remains s*a+N*b-S.
It shortens the table but increases W to (N/P)*sqrt(M), again yielding
(N/P)^(1/3). This new scaled cover and the complete conditional frontier
passed the separate Codex audit, retained in tasks-W030.json. Adopt its
precise supplied-entry/actual-label contract, integer rounding, tight widths
and complete public schedules. The full composition is conditional expected
Las Vegas time, not a deterministic theorem. All 23 delivery payloads and
18 frozen inputs match, including the external terminal manifest hash.
No numerical run or shared code change accompanied the new derivation.

[W027 is independently reviewed and dispositioned](findings/W027-parent-disposition.md).
Accept exact optimization of the supplied weighted coefficient envelope,
including legal precision reductions and constant-multiplier hybrids.
Substitute singleton coordinates first and also return the best shared c'=1
option; the smaller carry need not minimize a joint evaluator's cost.
The admissible comparison class requires normalized c' an ell-unit and
Q'>=ell. This remains a representation primitive, not a factoring gain.
The report's three non-report manifest entries match; its report hash
matches the exact prefix before a disclosed final handoff paragraph. The
complete delivered report has a separately recorded parent hash.

The [W025 review is dispositioned](findings/W025-parent-disposition.md).
Its multiplier bounds are correct, but known H^degree divisibility gives a
stronger truncation baseline in the advertised thin example: carry N^(39/120)
and occurrences N^(69/120), replacing N^(47/120) and N^(77/120).
The five-case certificate is finite identity evidence, not a fast ILP
implementation. All16 delivery payloads and2 frozen inputs matched; no
external terminal manifest anchor was supplied and no run was repeated.
Correct its wording: p!=1 modulo ell is equivalent to FILTER RETENTION of
the true leaf, not to its integer exponent being nonzero.

The parent [explicit consumer and frontier](findings/W025-consumer-and-cost-frontier.md)
groups anchors by Q' and shares carry babies. It still constructs M weight-pair
anchors and has the one-fifth cost envelope in that model. Varying c' loses
some nonlinear coefficient sharing, not this stride sharing. Its generic
anisotropic bounds are sufficient, not optimal for Hensel coefficients.
A projective chart attempt reduces chart acquisition but introduces a scaled
width; retaining the compensating congruence leaves a variable-modulus carry
problem that is NOT solved by its sparse notation.

[W026 is reviewed and dispositioned](findings/W026-parent-disposition.md).
Accept the affine multiplier's exceptional-residue tree with exact signed
endpoints, original-precision singleton fallback and paid branch widths.
Its generic size estimate loses to constant scaling. The final public
family must be FROZEN during collision localization: reacquiring a cheaper
representation does not preserve an already detected product collision.
All 18 local delivery payloads match. W026 and W027 are terminal; their
handles remain in tasks-W026.json and tasks-W027.json.

[W024 is accepted with explicit scope](findings/W024-parent-disposition.md).
The public PRIME-RESIDUE SIGN FILTER removes literal zero exponents without
a magnitude guard. The reviewed sieve ceiling is16*(bitlen(N)+1)^2, with
uniform chart acquisition costs and explicit small-target/range repairs.
At least half the old leaves survive, so the filter does not shorten carries.
All18 delivery payloads matched the externally supplied manifest hash.
Three focused RootCharts integer identities now compile;12 Python tests,
source screen, Lean build and axiom audit passed in the completed check.
See W024-parent-checks.json. Those theorems do not prove the prime schedule,
modular unit argument, ILP algorithm or a factoring complexity bound.

[W028's circuit and parity identities are independently checked](findings/W028-parent-disposition.md).
The finite rational Newton circuit matches the central-binomial prefix;
its numerator and denominator have exact degrees also modulo odd N,
because their leading coefficients are units. One parity split has an
explicit four-component circuit. Every exact arithmetic section retains
the denominator degree over Q; this is NOT a single-coefficient or circuit
lower bound and the positive-real proof does not cover finite fields.
All 14 local delivery payloads match, and tasks-W028.json is terminal.

The parent rejects the review's broad linear-scan comparator. A standard
[composite coefficient-or-factor baseline](findings/W028-composite-coefficient-baseline.md)
uses monic product/remainder trees in soft sqrt(m) work, returning either
binom(2m,m) or a proper factor. Its gcd localization and unit inversion are
explicit. This is Strassen-style prior art, not a new factoring bound,
and it does not consume the Newton circuit. The primary Bostan–Gaudry–Schost
paper explicitly treats composite rings. No experiment was repeated.

[W029 is now reviewed and dispositioned](findings/W029-parent-disposition.md).
Accept the semiprime formal degrees and the normalized derivative identity.
The scalar derivative H_N is already (F_N-G_N)/(2x) at unit x, so it does
not add information beyond the companion circuit output. Its exact zero
count is Z=(gcd(p-1,q-1)+gcd(p+1,q+1))/2-2 over each prime, giving a precise
CRT split probability; Z=0 at N=35. This is failure of that gcd test,
not of a separate gcd(x,N) preprocessing step or of factoring.
Do not adopt the review's nonsquarefree top-index extension (N=9 is a
counterexample), blanket extension-ring automorphism language, generic-prime
probability assertion, or global lower bounds on symbolic operations.
All 14 frozen input/source checks match; the parent read all certificate
source/output, including the 4,634-event finite run. No complete child
delivery manifest was supplied, and no experiment was repeated.
tasks-W029.json is terminal. Its formal-degree acquisition is still unpaid.

The [W023 disposition](findings/W023-parent-disposition.md) accepts the independent
exact degree result: every binary section path of the central-binomial series
has degree 2^(2^k), also modulo every odd prime and for nonzero polynomial
annihilators over odd composite moduli. The general-a theorem requires p not
dividing 2a. Sparse equations and ordinary polynomial circuits have narrower
representation costs; there is no lower bound for the single requested residue.
The task is terminal and preserved in tasks-W023.json; no certificate ran.

While that audit ran, the parent developed a [unit-safe Newton computation
and middle-coefficient recurrence](findings/W023-single-residue-computation.md).
Only 2 is inverted. It corrects W022 B's broad claim that modular acquisition
must reveal a factor first, but dense evaluation still costs roughly N and
the proposed compressed recurrence returns the original binomial target.
The identical finite-field cubic was deduplicated against W011 rather than
retested. A separate [direct-cover / folded-gap finding](findings/W023-direct-cover-and-folded-gap.md)
explains some old toy witnesses and rejects two attempted gains by cheaper
same-promise algorithms. Neither document supplies a complete improvement.

Both [W022 audits are now dispositioned](findings/W022-parent-disposition.md).
Accept valuation coverage, quartic root charts and balanced cost envelopes,
with exact signed endpoints. The old unbalanced Rmax guard fails on a growing
family; W024 addresses ONLY that guard. Accept the binomial splitter with its
exact no-carry condition and semiprime scope. Do not adopt blanket nonunit-
division impossibility, prime-power multiplicities inferred from radical
support, or literal equivalence of elliptic and norm-one group algorithms.
The 22 chart payloads and 27 binomial checksum entries match; the existing
26-case binomial certificate used 11,335 events and was not rerun. Task handles
remain in tasks-W022.json as COMPLETED.

Next substantive computation: try to combine several W030 digit buckets
in one paid product operation. Their cross terms depend on both bucket
labels, so independently solving each terminal rank-one product recreates
M work. A candidate must price that joint label interaction, rather than
assuming a sparse-polynomial or hidden-order equality oracle. Keep the
separate circuit-functional route available, but the W029 derivative test
is closed as a new scalar mechanism. Reviews restrict acceptance of their
own claims, not ideation. No shared solver or Lean code changed this turn;
the last required shared checks remain the passed W024 check.
Complete factoring improvement: NONE.

[W021](findings/W021-parent-disposition.md) is now independently reviewed and
accepted only as a supplied quadratic-product primitive. The exact bit bound
is L^(3/4+epsilon)*O~(log N), plus additive binary exponent setup. Use van der
Hoeven--Lecerf Theorem5.5 for Turing machines; KU Cor4.3 alone is a RAM citation.
Localization repeats setup O(log L) times. Practical constants are enormous;
linear phases have the stronger square-root comparator. The full factoring
coverage question remains open in this project. All 26 review payloads matched;
the frozen 8-case certificate passed at 3,873 events and was not rerun.

W021's coefficient-folding review is fully read and dispositioned too: support
and permutation identities survive, corrected r2/r3 collapse to Fermat, and
individual coordinates yield extra finite witnesses without a coverage theorem.
All 25 payloads matched; the frozen24-case certificate used18,668 events. Do
not conflate whole-vector content with coordinate gcds or inherit AKS factoring
completeness. Both W021 tasks are terminal; handles remain preserved.

The completed W020 reviews are now [dispositioned](findings/W020-parent-disposition.md).
Accept collision-to-annihilator recovery with <=2 expected trials under its
full coverage/nonzero-exponent/localization contract. This removes high-order
preparation and all-global-tag recovery; the explicit known one-fifth bound
remains. Accept annihilator amortization across supplied elements with canonical
matching and correctly scoped common-annihilator promises. Its recurrence and
interval sharing have prior-art comparators at the same cost. All 25 and 17
review payloads matched local manifests; no external full-manifest terminal
hash anchor was supplied. No experiments or shared-code checks ran this intake.

A different attempt is recorded in [W020](hypotheses/W020.md): use a known
square-class conic point to obtain a second class half. Rational line moves
only preserve the modular root up to a global sign unless a parameter gcd
already factors N. The pointwise integer identities are now proved in
Factoring/ConicParametrization.lean. The modular unit/gcd cases and class-group
interface are prose arguments, not formalized algorithms or lower bounds.
The primary Bosma--Stevenhagen halving method explicitly assumes the
discriminant prime-power root inputs; its source and reference-numbering
erratum are recorded with the stated read scope.

[W019 A/B](findings/W019-ab-parent-disposition.md) are now completed and
dispositioned. A supplies N-only coverage via S=u*p+v*q and a public m^2
root constraint. Its completed classical Las Vegas composition reaches
expected N^(1/5)*poly(log N), an already known numerical exponent with close
prior-art overlap, not a new improvement. A7 genuinely shares root calls
but leaves UV pair work, carries and the unbalanced U+V acquisition cost.
All 28 payloads/29 checksum entries matched. No experiment ran.

B's original per-sample half-success claim was WRONG for arbitrary pivots.
It is corrected in the hypothesis while the submitted version is preserved.
The accepted criterion is noncyclicity of the generated subgroup; persistent
larger-order pivots give <=4 expected fresh uniform samples. Odd annihilator
parts preserve cyclic subgroups and do not themselves bias that event.
The squarefree-semiprime extraction interface is accepted; the mechanism is
already known. All 24 payload hashes matched the local manifest, whose full
hash matches its checksum and terminal prefix. The single preregistered
certificate passed 11 assertions/4,454 events; parent did not rerun it.

[tasks-W019.json](tasks-W019.json) retains A/B as COMPLETED and now C as
COMPLETED (Grok 4.7). Its terminal summary was read: twist-product cancellation
does not overcome annihilator height; the reviewer reports no low-height norm
map. Full report/hash intake remains pending; do not promote its detailed
analytic/model assertions from the summary alone.
The earlier [root/carry continuation](findings/W019-root-carry-computation.md)
records the explicit binomial row product and why power-filter lifting does
not improve density. The new collision extractor changes its recovery
obligation but does not evaluate that row product for free.

Latest shared-code validation: scripts/check.sh passed all 12 Python tests,
source screen, pinned Lean build (10 jobs) and axiom audit after adding
Factoring/RootCharts.lean. The three new proofs check the scaled quartic series,
its bivariate truncation, and residual propagation. Their axioms are the existing
propext/Classical.choice/Quot.sound set. They do not prove valuation coverage,
root acquisition, product costs or a factoring bound. No Python solver changed;
no parent numerical candidate run or performance claim was made.

[W018](hypotheses/W018.md) is now independently reviewed and
[dispositioned](findings/W018-parent-disposition.md). Accept its expected
factor-or-powered-order primitive for arbitrary positive binary M and odd
composites with at least two distinct prime factors. Expected cost is
O~((bitlen M+sqrt B+1)*poly(log N)), retaining exact bounded order search,
the complete square chain and uniform-preimage failure-set proof.
Accept product-exponent sharing, with actual widths, tags and ceilings paid,
and the deterministic O~(K+sqrt(total occurrence length)) supplied-progression
product comparator. This resolves base preparation, not useful coverage.

The separate W018 extension review accepts the <=3 expected-trial norm-one
primitive on distinct odd semiprimes with the all-residue Cayley sampler;
its degree-gap proof and sufficient global two-dimensional injectivity
condition also survive, with their representation/order scopes.
The ordinary dependency is now discharged. The explicit table entries and
componentwise uniqueness obligations still cost work.
All 40 ordinary-review payloads/41 checksum entries and 17 extension
payloads/18 checksum entries matched their terminal anchors. The ordinary
reviewer's single frozen 21-case certificate retained 3,287 checks and
16,370 charged events with zero failed assertions; parent did not rerun it.
No Lean proof or new complete factoring improvement follows from this audit.
[tasks-W018.json](tasks-W018.json) retains both COMPLETED handles and briefs.

[W017](hypotheses/W017.md) is completed and
[dispositioned](findings/W017-parent-disposition.md). Accept the finite
Euler-log batching and exact square-conductor tail correlation with all
precision costs. An established Fourier/exponential-sum construction matches
the finite batch's asymptotic cost on equal inputs. Analytic tails and
factor extraction remain separate obligations; no shared search table
across different discriminants is supplied. All 35 payloads and the manifest
anchor matched. No experiment ran. [tasks-W017.json](tasks-W017.json)
preserves the COMPLETED task. W019 B/C are constructive responses, not
repeated checks of the same finite computation.

[W016](findings/W016-parent-disposition.md) remains accepted in its supplied
progression scope: expected O~(N^(1/5)*m^(-1/5)) for m<=N^(1/6), with paid
base acquisition in that regime and no N-only/novelty claim. Integer
coefficients, not merely integer values, are required by its transfer.
All 29 payloads/30 checksum entries were verified.

[W015](findings/W015-parent-disposition.md) retains accepted composite
halving, the capped O~(C_route+1+R+sqrt H+sqrt U) evaluator and full-gcd
localization. The literal interval representation misses its proposed
parameters. The later parent [valuation compression](findings/W015-valuation-compression.md)
changes that representation but still costs the N^(1/4) scale in its product
calculation; it has not received a separate independent audit.

[W014 disposition](findings/W014-parent-disposition.md) accepts A/B's scoped
results. C's original N^(2/7) claim dropped mandatory giant ceilings and is
withdrawn. Its COMPLETED Opus correction round is preserved in
[tasks-W014.json](tasks-W014.json), but its full 611-line report and delivery
hashes still await parent intake. Do not adopt expanded classifications or
the new N^(1/3) schedule from its terminal summary. Both failed preregistered
certificates remain; the parent also explicitly withdrew its own incorrect
Cayley-image objection. This intake backlog does not block W019 development.

The preceding [W013](hypotheses/W013.md) is fully dispositioned. Its original
A/B audits are completed in
[W013-ab-disposition.md](findings/W013-ab-disposition.md); all 19/19 and
23/23 delivery entries matched bytes and hashes. The reduced residual walk
maps to known continued-fraction machinery under the specified initialization;
arbitrary walks and mixed-sign probabilities are not thereby covered. The
quartic obstruction q*H^2<=5120*E*X survives review, even without the parent's
extra small-error guard. This is a scoped approximation result, not a
factoring lower bound. Exact integer recovery avoids modular root acquisition
but still pays for all candidate errors.

The parent then developed a
[shared hidden-period consumer](findings/W013-hidden-period-consumer.md):
transfer a true approximation error to an exponent modulo p-1, share a baby
table, and recover integer factors from full-modulus matches before removing
them. Its accepted conditional cost is K+sqrt(sum_i(2E_i+1)) up to polynomial
logarithms, with base/certificate acquisition paid. The linear budget recovers
the known N^(1/5) scale; higher-degree sufficient budgets do not improve it.
A rational-approximant normalization exposes the denominator-scaled error and
the exact-reciprocal degeneracy. This is not a new complete factoring bound.

[tasks-W013.json](tasks-W013.json) preserves A/B/C as COMPLETED, with all
original briefs and exclusive output prefixes. The
[C disposition](findings/W013-hidden-period-disposition.md) accepts the consumer
including prime powers, paid dyadic coverage and base acquisition. All 26
delivery entries matched hashes/bytes. The degree-four sufficient budget is
corrected from invalid-regime 11/40 to 5/18 after tolerance saturation; this
is still worse than the linear recipe and is not a lower bound. Signed/zero
normalized denominators and the ratio's nonzero domain now have explicit guards.

Checkpoint validation: scripts/check.sh passed all 12 Python tests, the
source screen, the pinned Lean build (8 jobs) and the axiom audit after adding
Factoring/ResidualNormalization.lean. Its five pointwise integer lemmas prove
error/recovery/exponent normalization and the nondegeneracy/zero cases only;
the complete consumer, useful certificate supply and complexity are not
formalized. No shared Python solver changed.

The preceding wave [W012](hypotheses/W012.md) was a different
starting point from finite-field concentration: correlated arithmetic
certificates and exact convex integer optimization above xy=N. Two
quotient certificates give an accepted affine lattice of determinant m^3,
retaining p mod m and pq mod m^2 jointly. A paid support minimum certifies
an exact factor-free interval; a midpoint rule gives a terminating N-only
baseline, but no improved query count is proved.

The parent derived a [central cap-width bound](findings/W012-convex-cap-width.md).
A chord across a sufficiently wide hyperbola arc necessarily contains a
point of the retained lattice. Consequently each connected convex empty
cap removes only O(N^(1/4)) candidate abscissas in the balanced range.
This prices full coverage by separate caps at an N^(1/4) scale up to
sieve density; it is NOT an early-stopping or general factoring lower
bound. The [geometry disposition](findings/W012-geometry-disposition.md)
accepts the proof with domain clipping, actual retained populations and
occupied-chart qualifications; it redirects work toward shared certificates or
an explicit factor-selective navigation rule rather than better tangents.

The parent also tested a genuinely different use of the support primitive:
product-descending navigation rather than covering every interval. One
preselected [exact certificate](findings/W012-navigation-trap.md) at
N=101*211 gives a closed nonfactor plateau with product N+1. Both adjacent
moves out increase product, and the gradient support update is a false
fixed point. This closes that specific descent rule, not every navigation
method. No numerical performance sweep or replacement instance was run.
A repair must specify paid barrier crossing or shared block computation.

[tasks-W012.json](tasks-W012.json) preserves four COMPLETED symbolic reviews:
A (affine lattice, exact support algorithm and convex-optimization theorem),
B/Opus (primary hyperbola-hull literature and precise count scope), and
C (new central-arc cap-width/covering proof), plus D (square-coordinate
relations and the exact slope sampler). All original briefs, handles
and assigned prefixes are retained. A/B/C's disposition corrects raw versus
primitive discriminants, normal-cone adjacency, large-modulus enumeration,
and the review's overbroad localization-only conclusion. The 2025 full-hull vertex
bound must not be imported as a bound on clipped central arcs or finding
one factor; those scopes are expressly separate.

D's [selector disposition](findings/W012-square-selector-disposition.md)
accepts the congruence and expected-cost binary-search sampler. The reviewed
telescoping bound gives P(E)<=4Q(E) for every interior event throughout the
strict-convexity regime; Q is a mathematical curvature comparison law, not
a free sampler or useful-row supply theorem. Repeated indices repeat rows.
The construction gives no factoring improvement. Forty fixed certificates
are not an asymptotic experiment or a Lean proof. No further parameter
sweep is selected for these closed claims.

[W011](hypotheses/W011.md) is fully dispositioned, both tasks terminal.
Its [algebra disposition](findings/W011-two-color-disposition.md) accepts
the fixed-map identities and stopping laws, with raw/accepted and global
chart weights explicit. The cubic prime-average root theorem has fixed
depth only; the family has no proved basin-supply theorem. Its [basin
screen](findings/W011-basin-disposition.md) failed: 0/16 qualifying
parameters on each primary pair, with every scheduled case completed.
The finite rejection is not an all-family asymptotic impossibility claim.
[tasks-W011.json](tasks-W011.json) preserves both completed briefs/results.

The parent [implicit-discriminant note](findings/W011-implicit-discriminant.md)
derives a cheap critical-orbit scalar for an exponential-degree iterate,
then identifies its loss: only O(k) random-target opportunities in the
unicritical case. This distinct computation is not independently reviewed;
it does not supply a speedup or a general scalar-product lower bound.
No shared solver or new Lean theorem has been selected.

[W010](hypotheses/W010.md) is now fully dispositioned (A–D terminal).
The norm-selected cubic has strictly positive expected residual-collision
drift on every symmetric law with a legal pair; this resolves its sign,
not its rate. The [norm-envelope disposition](findings/W010-norm-envelope-disposition.md)
accepts the adaptive O(k/p) mean-mass bounds through 81^k<=p and the
literal training/one-pin/probe success bound, with accepted-pin mean
m+v/s and all rejection weights. It is not an all-depth or actual-work
lower bound. The [Jacobi disposition](findings/W010-jacobi-disposition.md)
accepts unmasked new roots but gives symmetric weighted laws destroying
universal residual drift, without asserting reachability.

The [batch-extraction disposition](findings/W010-batch-extraction-disposition.md)
accepts duplicate-safe monic product trees, recovery from full product
gcds, the weighted birthday law under w_p,w_q<=1/2 and a dyadic schedule
with finite expected cost. A stronger variance tail makes one fresh batch
per width sufficient; constant success alone would not. This prices the
conditional detector at (k+1)/sqrt(rho)*poly(log N) for a length-k map.
Paid useful-map acquisition, including its probability, remains the
bottleneck. [tasks-W010.json](tasks-W010.json) retains all completed briefs,
handles and dispositions. No accepted claim establishes an end-to-end
factoring improvement. W011 changes both the sampler and computation;
W010's envelope does not transfer to it.

[W008](hypotheses/W008.md) remains the scalar-computation branch. A/B/C are
terminal, with complete prompts/handles preserved in [tasks-W008.json](tasks-W008.json).
The [four-list disposition](findings/W008-fourlist-disposition.md) accepts
pairwise useful supply, one-path full-gcd extraction, the N-only schedule
and a repaired monic K^2*poly(log N) control. Paid input sampling changes
the hypothetical exponent to max(1,alpha)/4. Independent-label restart
accounting now uses BOTH factor orientations, rho=1/p+1/q-2/N; it still
closes only the explicit materialize-first implementation.

The [affine-grid disposition](findings/W008-affine-grid-disposition.md)
accepts a five-residue generator and an exact block evaluator at the same
sqrt(p) scale. A new K>=p covering argument fills the N-only scheduling
gap. Per-coordinate dyadic splitting makes recovery work geometric. It
corrects the review's use of BY Theorem 5: N_term>d fails for length K
and degree K^3. No fast slicing algorithm follows from that theorem.
The separate [boundary recurrence note](findings/W008-grid-boundary-recurrence.md)
remains provisional; its finite-field part has not been independently audited.

The parent developed a concrete matrix-compression test. Its
[disposition](findings/W008-displacement-disposition.md) accepts that one
multiplication of two rank-2 displacement factors can produce rank K.
This closes a dense, bounded-rank generator state, not scalar computation:
the witness itself has norm 1. The tested scalar norm tree recreates K^2
coefficients or pays K^4 direct work. Direct compact-grid products and other
implicit scalar algorithms remain open; no sub-K^2 evaluator is supplied.

The parent-led acquisition branch is [W009](hypotheses/W009.md).
A's [disposition](findings/W009-pinned-disposition.md) accepts the exact
three-anchor sampler: its acquired involution is biased by current merger
mass, without measuring that mass. Both root/pole atoms and all failed
charts are included. Flat-law nondecrease is accepted; a weighted F_7 law
refutes universal nondecrease, without a reachability claim. Stopped retry
costs use C+R (clean or factor), not C alone. No persistence theorem follows.

The parent then developed a [two-anchor reciprocal update](findings/W009-reciprocal-two-anchor.md).
It replaces pinned shifted energy by ordinary multiplicative energy and
uses separate root/pole gcds. B (Opus) completed; its
[disposition](findings/W009-reciprocal-disposition.md) accepts the exact law
and extraction. It rejects the review's claimed impossibility of a large
two-color partition, unsupported frame-alignment rate, and unqualified
full-status-vector failure formula. An exact reachable F_5 partition is a
counterexample to the structural claim, not asymptotic performance evidence.
C's [simple-pole disposition](findings/W009-simple-pole-disposition.md)
accepts second-step residual collision mass 3/p+O(1/p^2), the uniform
early-depth envelope and its literal raw-budget success scope. It is not
an actual-work lower bound. D's [power-reset disposition](findings/W009-power-reset-disposition.md)
accepts the four-fiber obstruction: earlier geometric powers do not accumulate
through a distinct-anchor reciprocal fold. It repairs the original support
parity and three-fiber wording; finite-field coincidences remain separate.

E's [escape disposition](findings/W009-escape-disposition.md) accepts the
odd-fold laws and the coherent 2-isogeny identification. The exact curve-plus-
twist kernel count shows saturation at the 2-primary part for that schedule.
It corrects an endpoint k=0 error, limits fixed-group and dominance claims,
and leaves the secondary-source isogeny classification unpromoted. The
dual schedule duplicates W001; no new complexity improvement follows.
[tasks-W009.json](tasks-W009.json) preserves all A–E terminal handles.
Distinct samplers require distinct laws; none of these negatives is a
general factoring lower bound. The cubic W010 direction is independently
derived and does not inherit the reciprocal envelope.

[W007](hypotheses/W007.md) remains active. The parent is developing actual
compressed polynomial evaluations and distinct finite-field acquisition rules.
The explicit eight-root, three-stage rational polynomial remains a finite
construction, not an asymptotic factoring result.

A's [fixed-cover disposition](findings/W007-fixed-cover-disposition.md)
accepts the full order-128 groups, constant field Q and genus 25. A rational
one-parameter formula for that fixed cover's full splitting data is closed;
existence of a further split value is not. Branch collisions at p=17 prevent
transferring the characteristic-zero cover calculation to all p>13.

B's [varying-fiber disposition](findings/W007-varying-fiber-disposition.md)
accepts the additive-triple and symmetric-PTE composition conditions, but
closes all four displayed Choudhry families by twelve modulo-7 certificates.
No sixteen-root construction was obtained. Parent also derived a concrete
[rational angle progression](findings/W007-angle-progression.md); it yields
only a zero value and the already-known quartic fiber, so that proposal is
symbolically rejected, provisionally pending independent audit. Do not
increase searches within these closed parametrizations.

The user explicitly authorized Claude Opus 5.5 and Grok 4.7. Exact live
catalog IDs were verified and both used through T3. C (Opus) completed:
the [tau disposition](findings/W007-tau-acquisition-disposition.md) accepts
the short integer-root conversion and conditional conjecture link. It
corrects the report's modular-only/input-dependence statements, rejects
its claimed universal root-height requirements, and repairs its rho cost
threshold. Read the disposition rather than adopting the child report
unqualified. No original Lipton factoring theorem was verified.

D (Grok) completed; its [disposition](findings/W007-residual-dynamics-disposition.md)
accepts the exact residual drift, reachable negative drift and depth-three
mean, and corrects CRT/stopping and cost-regime overclaims. A/B/C/D are
terminal in [tasks-W007.json](tasks-W007.json). Do not repeat the finite
tables or promote the unstopped root law to a survived-history law.

E/F are now terminal and dispositioned. The
[component disposition](findings/W007-component-disposition.md) accepts
factorization, irreducibility, component means and a sharper intersection
bound. It corrects the review's survival-conditioning, nominal-budget and
all-depth extrapolations. The [Fourier disposition](findings/W007-fourier-envelope-disposition.md)
accepts E[m_j]<=j^2+1 through 2^k<=sqrt(p) and at least p/(40k)
expected ACTUAL multiplications for its specified fixed-k/t restarted
implementation, p>=1024. This is a scoped failure of that evaluator to
match the sqrt(p) control, not a bound on later depths, changed acquisition
rules or factoring. All W007 A–F prompts, results and handles remain in
[tasks-W007.json](tasks-W007.json). No repeated audit is needed.

The parent developed a distinct [pair-selected update](findings/W007-pair-selected-merging.md):
choose a=P(r)+P(s), so two actually sampled fibers merge. Its provisional
growth law uses fourth-order additive energy. A local interval law would
give a large one-step gain, but the obvious small-integer generator makes
the collisions global at both primes and returns only 1 or N. The next
gate is actual componentwise acquisition of useful additive structure,
and preserving it across updates, with all training and probe costs paid.
The favorable interval formula is not grounds for an empirical screen.

Keep a small diverse reserve: coefficient-information extraction and
off-chart norm acquisition remain alongside the active root/collision
branch. Rational full splitting is a bounded algebraic probe; neither a
genus obstruction nor the tau connection is a general factoring lower bound.
No new candidate experiment or shared code/Lean change in this checkpoint.
The complete research objective remains ACTIVE; verified improvement NONE.

All W006 A–E tasks are terminal and dispositioned. The
[map/batch disposition](findings/W006-map-batch-disposition.md) accepts the
transition and stopped sign law but closes the fixed scalar-capture menu:
for every p=5 mod12 there is no extra ingress at any depth. The 60-case
screen was omitted; ALL entries are UNKNOWN/UNSTARTED. There are NO saved
transition tables or empirical graph data. Fresh uniform parameters have
only linear rare-hit opportunities and do not fix this branch.

The corrected batch consumer globally deduplicates, evaluates P and P',
and uses one bounded omitted-self descent. Its K*poly(log N+log K) bit
bound and explicit constant-probability law are accepted for distinct odd
semiprimes, giving only the known sqrt(p)*poly(log N) identity control.
Prime powers are excluded. Full acquisition/survival costs remain in the
energy comparison. The parent's square-first alternative is provisional;
the accepted derivative repair already suffices, so no duplicate audit is
selected solely for that alternative. Historical handles remain in
[tasks-W006.json](tasks-W006.json).

The [coefficient disposition](findings/W006-coefficient-disposition.md) and
[reflection disposition](findings/W006-reflection-disposition.md) remain
authoritative. The fixed coefficient menu fails at 2701; the large certificate
instance remains UNKNOWN. The regular two-reflection chart collapses to a
scalar gcd; normalized off-chart cancellations are not ruled out. These are
scoped results, not global lower bounds. Preserve coefficient-information and
off-chart acquisition as diverse reserve directions.

All W005 tasks A–F are terminal and dispositioned. The
[blinded Norm2 sampler](findings/W005-blindnorm-disposition.md) replaces two
N-record joint-wrapper setup lists with polynomial bit work and streaming space.
It changes the complete reference envelope from O(N_0^(3/2) polylog N_0) to
O(sqrt(N_0) polylog N_0) using old gcd successes only; it improves no established
factoring bound and does not solve the standalone N,R-only Norm2 contract.
The [compatible-field disposition](findings/W005-compatible-disposition.md)
accepts the parameterization but shows its compatible parameter already yields
a modular square root. Global branches using x return +/-x. It also supplies
a paid polynomial clean-certificate law and a known-scale N^(1/4) block-product
control; neither supplies useful new packet mass.
A/B/D's [point/quaternion disposition](findings/W005-point-quaternion-disposition.md)
and C's [strip disposition](findings/W005-strip-disposition.md) remain authoritative.
Full prompts and all historical handles remain in [tasks-W005.json](tasks-W005.json).

Continue independent constructive research while the live W010 audits run. Each next candidate
must identify the computation it replaces, hidden costs, and a decisive falsifier.
Do not repeat fixed experiments or spend turns waiting when independent work
remains. Verified new complete factoring improvement remains **NONE**.

W004's construction and independent review are terminal. Its scoped results are
accepted with the conic denominator condition and execution completion in
[W004 disposition](findings/W004-disposition.md). The review's elementary coverage
lemma is accepted; the proposed small screen is declined because early row
checks already guarantee its coverage. No test ran and no useful mixed-packet
supply or complete factoring improvement follows. Original reports and evidence
are preserved. The parent verified all 42 review input records and 58 delivery
entries. Historical handles remain in [tasks-W004.json](tasks-W004.json).

All five W003 tasks are terminal. Lens A, Lens B and the parent norm gate retain
their accepted scoped dispositions and corrections. The source-only Shallit
follow-up below remains unresolved; do not repeat its failed endpoints.
E added only its authorized scratch distribution evaluator and reran all project checks.
No new shared solver implementation or Lean source change is selected in W005.

The coordinator read all 511 Lens A lines and all 572 Lens B lines, preserved
byte-identical submitted snapshots, and verified their original evidence.
Lens A has 29 frozen inputs and 32 delivery entries; Lens B has 19 inputs,
23 source identities and 54 delivery entries. The separate intakes are
[quadratic construction](findings/W003-twisted-intake.md) and
[source/reduction gate](findings/W003-root-priorart-intake.md).

The explicit quadratic lift has a reviewed real-sign obstruction to both mixed
targets at every row cap, with only earlier gcd/root-recognition successes.
The coordinator consumed all 667 review lines and verified 66 input snapshots
and 72 delivery entries. Its exact success counts, literal exponential work
and pruned complete cost are accepted at their local-program scopes. Read
"square root of unity" at original line 425; original evidence is unchanged.
The source lens supplies a reviewed Dixon-scale random-twist integer
construction with complete expected L_N[1/2,3sqrt(2)] cost, together with
corrected norm/involution and localized-recovery deductions. The coordinator
consumed all 905 review lines, verified 76 input snapshots and 89 delivery
entries, and accepted the certified B construction, full stopped-tape
coupling, rounded supply proof, sequential cubic schedule and paid wrappers.
Abstract target attainment and recoverability are separate predicates;
rational norms distinguish the extension-square bit when Norm(alpha) is
nonsquare. The small-R bound needs its cutoff domain. Original evidence is
unchanged. This source submission is not a review of Lens A. No new
factoring improvement is established. No NFS supply theorem transfers from
the integer coupling. W003 remains symbolic/source work only: no experiment,
implementation or Lean action is selected.

The [parent norm gate](findings/W003-normgate.md) gives a reviewed different
quadratic generator: from a verified modular representation u_0^2+v_0^2=5R,
construct f(T)=T^2-sT+4R^2 with s a lifted sum of two squares. It has positive
conjugates, a simple modular root and an explicit relative norm certificate.
An exact pair of integer-square tests handles alpha square in its field.
Its finite Norm2 reference costs O(N n^2) time and O(N n) bits on fixed
multitapes; no faster all-input bound is accepted from abstracts. The
coordinator consumed all 322 review lines and verified 18 frozen inputs,
30 review delivery entries and 16 original delivery entries. The correction
gives explicit rows (t,u),(v,1), where t=2R:
Q(alpha)=(t^2-u^2*alpha)*(v^2-alpha)=alpha*(v^2-alpha)^2.
The one-field target is attained. Conjugating the same field cannot give the
opposite ordinary-square target. An independently selected second field,
useful success law and complete cost remain missing. Shallit/BGH primary
passages retain their conditions; AEM's full theorem remains unretrieved after
six bounded reviewer searches. Original note, review and manifests remain
unchanged. See the governing norm-gate disposition above.

A separate bounded [Shallit source follow-up](findings/Norm2-shallit-source-note.md)
identified the exact TR85-001 citation and a related 1986 paper, but obtained
neither full pertinent theorem/algorithm. The retrieval limits are recorded;
no faster Norm2 guarantee or changed W004 cost is accepted. Do not repeat
the same failed endpoints automatically. This was separate from the live review.

The [frozen W004 brief](hypotheses/W004.md) and complete
[construction](findings/W004-biquadratic-construction.md) remain unchanged.
Their selector, packet algebra, localized recovery, genera and conservative
costs are accepted only with [the disposition](findings/W004-disposition.md).
No useful witness supply is proved. The reference complete expected upper
bound O(N_0^(3/2) poly(log N_0)) relies on old gcd successes and paid Norm2;
it improves no established factoring bound. W005 changes the computation under
study rather than importing a free point finder or a faster Norm2 claim.

H027–H031 submissions and reviews are complete. The coordinator
accepted their scoped deductions after local repairs; none supplies a new
complete factoring bound. H029 now provides a reviewed construction with
coverage and cheap visited-leaf recovery, while its fast interval product
remains missing.

All three W002 constructors and independent reviews are complete under the
[frozen brief](hypotheses/W002.md). The coordinator accepted the scoped results
with the corrections in their dispositions. None establishes a new complete
factoring bound. All six task handles are terminal with no pending runs.

| Completed lens | Registry | Authoritative disposition |
|---|---|---|
| W002 A: paired residuals | [tasks-W002.json](tasks-W002.json) | [Disposition](findings/W002-residual-disposition.md) |
| W002 B: adaptive CFRAC base | [tasks-W002.json](tasks-W002.json) | [Disposition](findings/W002-adaptive-disposition.md) |
| W002 C: Ward norm tensor | [tasks-W002.json](tasks-W002.json) | [Disposition](findings/W002-ecm-disposition.md) |

H030's exact Newton-cubic realization has now passed independent review at its
stated scope and is closed as a speedup: its outer root forces Omega(M^(1/3))
explicit records. The finite procedure costs M^(1/3)*poly(log M). The
degree/exception extension counts separately materialized dense lists and
explicit exceptions only. The coordinator consumed all 615 review lines,
verified 36 frozen inputs and 41 delivery hashes, and adopted three cost/notation
clarifications. Original submissions and manifests are preserved. No algebraic
repair was needed. RootProduct remains missing; no experiment, implementation
or Lean change follows. tasks-H030.json is complete.

The parent completed the [full-source ECM gate](findings/ECM-priorart-li2006-note.md).
Li's cyclic-polynomial special-form reduction is existing prior art; its stated
cost still multiplies curve count and scalar bit length. The cited success
argument retains independence assumptions, and the plus-case evaluation needs
its parity restriction respected. No new final-product recurrence follows.
Do not repackage that reduction or rerun H009's same sparse recurrence.
W002 C must supply a concrete state and transition, including cross terms;
a norm or resultant symbol alone is not an algorithm.

H031's independent review is complete. Its repaired adjacent-rotation trial,
exact failure-inclusive success identity and conservative L_N[1/3,3+o(1)]
per-trial upper bound are accepted at their stated scope. The coordinator
consumed all 702 review lines and verified 24 frozen records, 38 owned-artifact
records and 39 delivery hashes. Four mathematical/specification/cost/prior-art
completions clarify denominator-cleared reduction, fixed execution order,
variable-size root costs and the distinct sampling law. Original submissions
and intake/source manifests remain preserved. The probability identity still
has no proved useful-mass lower bound, so it yields no successful factoring-time
bound. The promise remains distinct Blum semiprimes. See
[H031 disposition](findings/H031-disposition.md); tasks-H031.json is complete.

W002 A changes the product interface explicitly to use d|M and permits a
verified proper factor on nonunits; it must prove its own complete recovery
and cost. W002 B must construct and charge an N-dependent relation universe,
without importing smoothness or productive-root mass. Each child develops one
actual realization and a decisive limitation, independently of the other drafts.
This wave is symbolic/source work only. No experiment, implementation, Lean
change or H032 candidate is selected by this wave. Its reviewed on-paper
results have the scopes below. The research objective remains unchanged.

W002 A's constructive report is complete. The coordinator read all 414 lines,
verified 17 frozen inputs and 27 delivery entries, and preserved the identical
original submission. Only current mutable STATE differs from its saved input.
The report derives e<8K<M, paid elimination of nonzero nonunits, and recovery
from any original zero row. Its concrete factor-or-UNIT interval-envelope
search returns the known N_0^(1/4)*poly(log N_0) scale; it does not supply the
desired sub-1/5 product or decision. The independent review is now complete:
all 557 lines were consumed, with 48 review inputs and 63 delivery entries
verified. The coordinator accepted its scoped bounds, conditional reduction,
factor-or-UNIT contract and complete N_0^(1/4) cost without algebraic repairs.
The explicit dense construction is closed as a speedup, with an unbounded
continuing N_0=M family establishing its representation-specific obstruction.
See [disposition](findings/W002-residual-disposition.md). No general factoring
lower bound follows. No experiment is selected, and original submission,
intake and source/delivery manifests remain unchanged.

W002 B's constructive report is complete. The coordinator read all 495 lines
and verified 22 frozen inputs, 42 delivery entries and 10 primary records.
The report gives a CFRAC residual stream, adaptive coprime-base construction,
and signed square-kernel basis extractor. It claims exact failure for every
cap on an infinite period-one composite family, even with arbitrarily many
smooth dependencies. Its L_N[1/2,3] envelope is a finite-trial cost only.
The 693-line review is complete; 69 review snapshots and 78 delivery entries
verify. The coordinator adopted its literal-pair support proof, narrowing the
H026 scope separation, and its sequential tape schedule and complete fixed-list
failure certificate. The all-cap failure is accepted; it does not cover all
adaptive generators or imply factoring hardness. See
[disposition](findings/W002-adaptive-disposition.md). The unchanged original,
intake and retrieval limitations are preserved.

W002 C's constructive report is complete. The coordinator read all 518 lines
and verified 20 frozen inputs, 30 delivery entries and 10 source-artifact
identities. The explicit closed Ward tensor stores 8^s residues and expands
16^s transition terms; its factored representation is ordinary per-curve
scalar evaluation. The report includes all gcd descent and exact raw-word
success identities, but no positive uniform useful-mass bound. The separate
review is complete: 612 lines consumed, 46 review snapshots and 58 delivery
entries verified. Five adopted corrections specify evaluator/driver domains,
cache and label access, a sequential scalar fallback, exact comparison
quantifiers and saved lifecycle evidence. The scoped invariant, recovery and
success identities are accepted through the authoritative
[addendum/disposition](findings/W002-ecm-disposition.md). The literal tensor
and retained-factor realizations remain closed as additive speedups.

Both B and C retain verifying snapshots of the mutable STATE and synthesis,
whose current versions now differ. No frozen evidence or original submission
was edited. All three W002 realizations miss the target as submitted; their
narrow reductions and closures are now accepted only as corrected in their
dispositions. Original provisional labels remain historical, not current status.

The coordinator also completed a bounded [comparison-source refresh](../docs/SOURCES.md#w002-comparison-refresh--2026-10-08).
The working factoring benchmarks are unchanged. Altman's 2025 simultaneous
polynomial factorization/root-finding results are now registered with their
distinct parameter costs and read scope; no uncharged splitting-field or
unknown-prime oracle is inferred. This is source work, not a new candidate.

The subsequent [CM source gate](findings/CM-priorart-gate.md) also closed the
immediate novelty question: scalar-N anomalous curves and symbolic class-ring
computation are existing special-purpose methods. Primary construction bounds
retain discriminant dependence and stated qualifications. Useful N-only
discriminant selection and complete proper-factor success are not supplied.
No new candidate or experiment follows; do not repackage this known route.

H021 and H022 reviews completed and their results were consumed. H021's
localized recovery correction is accepted. H022's fixed-stratum mathematics
passed independent review; the coordinator checked and adopted the explicit
uniform/adaptive-yield/mesh repair for its mixed-stratum statement. Both are
scoped mathematical results, not factoring speedups.

H024 and H025 also completed independent review during this wave. H024's
sharper cutoff, exact population upper bound and model-qualified optimizer
costs are accepted. H025's input-density consequence is accepted after a
fixed-epsilon wording correction and acceptance of H024's count dependency.
No code, experiment or Lean change accompanied these analytic results.

H023's review has also completed. Its finite geometry and primitive candidate
population are accepted, and its optimized constants are recorded only as
conditional models. The special-form factoring claim is closed without a
new algorithmic improvement. Original proposer/intake bytes are preserved;
the rotation citation now includes Kleinjung section 6.7.

H026's review has completed and the scoped theorem is ACCEPTED without
mathematical corrections. Its original draft and source manifest are preserved;
two scope clarifications and the uniform-union qualification are now explicit.
The exact low-energy/base-smooth universal supply question is closed negatively.

Next: consume the W004 independent-review notification using the saved handle,
read the complete review and evidence, and disposition its claims, corrections
and finite-test recommendation. The constructor's final intake and new review
launch are complete. W003 Lens A, Lens B and parent norm-gate scoped dispositions
are complete. Do not promote W004 deductions before independent review.
Do not duplicate live work. No W002 realization survives as a speedup, so do
not implement or enlarge its existing screen. Preregister any later decisive
computation separately, preserving the distinction between relation supply
and productive factor recovery. W002's scoped closures are not impossibility
results for other algorithms.
Each new major deduction requires independent
review before acceptance. Follow RESEARCH_TEAM.md for subsequent rounds with
full context and unresolved objections. The parent owns shared code and checkpoints.

H019's one frozen trial finished in 5.834619 seconds. All five controls were
correct; the four research cases gave one count certificate and three unknowns,
with no errors, timeouts, verification failures or unstarted cases. Only the
262144-bit input passed the count inequality; both largest were required, so
the registered experiment is INCONCLUSIVE. Its independent review has now
ACCEPTED the finite implementation and one degree-52 upper-count certificate,
checking all nine outcomes and 115 research disks in a separately frozen
3.500754-second exact replay. The three unknowns remain unknown. The original
source, criterion and evidence remain unchanged; these inputs have no semiprime
or hard-factor promise. tasks-H019.json is complete.

H020's full independent review ACCEPTED its exact weighted primitive count,
conditional exponent <=9/5, quantitative margins and polynomial-bit certificate,
without required corrections. All 18 review file hashes match. Uniform
geometry and useful yield remain unproved. See its disposition below.

H021's exact pseudo-polynomial optimization, bounded-delay enumeration,
counting/unranking and sampling constructions are accepted after fixing
optimizer recovery above the energy cutoff. Prefix predecessors remain
valid; capped suffix recovery is restricted to minimum <=E. The original
draft is preserved. Polynomial scope requires polynomial numerical ranges.
No implementation, finite experiment or useful-yield theorem exists for H021.

H022's accepted conditional relaxation has infimum c³=32(1+gamma)/9 for
actual f-height gamma in [0,1]. Its mixing statement now requires fixed
positive b, compact height ranges, uniform root geometry and errors, distinct
paid attempts, a strategy-valid aggregate expected-yield law, and a vanishing
norm mesh (or justified ordered limit). The coordinator checked the review's
repair and exact mesh-error inequality. This is no factoring lower bound.

H023's ordinary-base family f(X)=(X+1)^(d-2)(X²+M+1)+1 has a reviewed
irreducibility/separation proof, attained primitive population and exact
counterexample to dropping H022's geometry hypothesis. The original 16/3,
degree-halved 40/9 and fixed-s binomial 32(s+1)/(9s) cubes are conditional
model values, not full factoring bounds. Different optimal degree scales
do not imply fixed-input dominance; the sparse-family scope is explicit.
No new special-form factoring algorithm is accepted.

H024's accepted feasible cutoff is 0<E_star<40ell² instead of the original
loose O(ell^4). With a standard sieve and the stated rational logs, one exact
optimizer is tilde-O(ell³) in the charged indexed-memory model; the conservative
multitape DP remains tilde-O(ell^6). Counting and all useful outputs cost extra.
The exact diagonal population is <=exp(11E^(1/3)), so the accepted set has
at most exp(O(ell^(2/3))) vectors. This proves no smoothness density.

H025's accepted finite union count holds for any selector within that common
prime/weight/energy universe. For each fixed 0<epsilon<1, the fraction of all
ell-bit inputs admitting |u-Nv|<=N^(1-epsilon) from this cutoff is bounded by
exp(-epsilon*log(2)*ell+O(ell^(2/3))) and tends to zero. This is an upper
density bound, not an asymptotic equality or factoring lower bound. It does
not extend to every o(N) threshold, restricted input sets without their own
normalization, adaptive bases without a bounded union, or smoothness at larger
residuals. Original reviewed drafts are preserved; no equations needed repair.

H026's accepted theorem answers the exact H024 review's all-input inverse-
polynomial p_ell-smooth supply question negatively. In the common aligned
q<=40ell² universe, |w|<exp(177ell); a finite Euler product bounds possible
base-smooth values by exp(o(ell)). Vector/residual pairs therefore permit only
exp(o(ell)) qualifying ell-bit N. Verified primary Rosser–Schoenfeld estimates
give a balanced squarefree-semiprime ensemble of size Omega(2^ell/ell²).
For every sufficiently large ell, most members have NO base-smooth residual
in their entire nonempty low-energy set. No random-smoothness premise is used.
This is an input-density theorem, not H024's conditional per-attempt law or a
factoring lower bound. Larger bases, energies, changed weight alignment and
post-LLL/TN domains remain outside its scope. No efficient failing-input
constructor or practical threshold is claimed.

The parent verified all 57 H019 sealed files, 13 frozen sources and six frozen
input objects, plus the completion link. Current originals differ only in the
legitimately mutable STATE. ./scripts/check.sh passed after H019's code handoff:
12 Python tests, source screen, seven-job Lean build and axiom audit. These
shared checks do not validate the new research certificates by themselves.
The H019 reviewer performed one separately frozen arithmetic replay of archived
witnesses, without rerunning root proposals or original modules. The parent
verified all 76 review-frozen files, 37 owned hashes, 30 sealed review files and
the completion link. H021/H022 source snapshots and review hashes also match;
all 19 H022 completion input/output hashes were checked before edits. No shared
code or Lean changed for these repairs. H024's reviewed source snapshot matches;
H025's submitted snapshot and review hashes were verified before its scope repair.
H023's original report/intake and review hashes were checked before its citation
and status edits; no algebraic correction was required. All 23 H026 manifest
entries and the review hash matched before its acceptance edits. No code or
Lean change accompanied H020–H026's latest analytic work. The parent subsequently
read all 680 H027, 808 H028 and 300 H029 report lines. Before checkpoint edits,
all 17+12 H027 manifest entries, all 17+13 H028 input/output entries and all
21+2 H029 frozen-input/delivery entries matched. Original drafts are preserved.
H027–H029 also made no shared code or Lean change. All 630 H027 review lines
were consumed and its 34 frozen-input plus 52 artifact hashes matched before
six local repairs were adopted, including the sequential C4 access proof.
All 731 H028 review lines were consumed and its 34 frozen-input seals plus
47 owned-artifact entries matched; three local ledger repairs were adopted.
All 622 H029 review lines were consumed; 40 frozen inputs and eight delivery
hashes matched. Its parameter-width, pair-order, root-initialization and
index-cost repairs are adopted. H030's exact polynomial-block construction and
scoped obstruction are independently accepted after three cost/notation
clarifications. H031's adjacent-rotation trial subsequently passed scoped review
with the corrections recorded in its disposition.
No improved algorithm is accepted. Do not implement the closed low-energy route.

## Completed broad wave W001

All seven tasks completed and their results were consumed. Exact handles and
completed states are in tasks-W001.json. Six reports supply 24 mechanism cards;
the seventh is a primary-literature baseline ledger.

Read [the synthesis](findings/W001-synthesis.md) for the full disposition table,
shortlist and next branches. A report's mathematical derivation is not
automatically an independently accepted theorem. No candidate has yet supplied
a new end-to-end complexity bound.

The baseline ledger separates heuristic GNFS (including the better cited
Coppersmith constant), rigorous randomized complete factoring, deterministic
N^(1/5)-scale methods, special families and quantum algorithms. Conditional
N^(1/6) deterministic ambitions do not beat heuristic GNFS asymptotically and
are not polynomial in input bit length.

## H003: explicit factor-sum residue sets closed

The independent review accepts the exact local cardinality and uniform
M^(1-o(1)) full-output bound. The known two-list continuation costs
N^(1/4-o(1)) in the stated balanced non-close regime. This is a representation
obstruction, not a factoring or implicit-query lower bound.

[Disposition](findings/H003-disposition.md),
[review](findings/H003-independent-review.md),
[frozen evidence](experiments/H003/result.json).
tasks-H003.json is complete. Reopen only for a new costed implicit primitive.

## H004: reduction retained, tested cover rejected

Both tasks completed; tasks-H004.json records them. The prime-cover reduction
with costed interval products and executable leaf factoring is correct and
implicit in the source framework. Multiplicities must be stripped from original
N. No cheap cover/leaf implementation follows from the reduction itself.

The power-shift cover failed all 14 nominal cases. Its preregistered exponent
repair succeeded only at m=2; all other 339 exponents failed. All 360 cases and
missed primes are retained. Do not expand the shift grid merely to fit examples.

[Disposition](findings/H004-disposition.md),
[reduction review](findings/H004-reduction-review.md),
[construction/evidence links](hypotheses/H004-prime-cover-construction.md).
The frozen preregistration, source and result hashes were rechecked and match.

## H005–H006: small exhaustive-tree relaxation closed

H005 degree-two diagnostic passed its registered finite threshold, but all
intervals contained at most two integers. The parent therefore classified it
inconclusive and strengthened the question; no performance claim was accepted.

H006 uses degree five and constructs valid tangent/secant relaxation witnesses,
expanding only a certified subtree. All 20 registered instances completed.
At K=36 the median visited count is 22,337 and median tree fraction 0.17046.
The rejection threshold was 0.5, so the frozen outcome remains **inconclusive**.
There are many spurious feasible points; their finite counts do not establish
an asymptotic or early-stop factoring lower bound. Failures to certify a node
are unknown, not proofs of infeasibility.

[H005 finding](findings/H005-quadratic-screen.md),
[H006 finding](findings/H006-certified-subtree.md),
[H006 frozen evidence](experiments/H006/result.json).
Source and protocol hashes were rechecked and match. The H006 independent
review completed, replayed all 20 inputs and validated 53,108 certificates.
Its separate mathematical derivation gives Theta(R³) full-tree nodes, uniformly
for the diagnostic boxes and on a broad range of actual clipped boxes. The
coordinator checked the counting and reachability arguments and closed the
proposed R*poly(K) exhaustive-tree route. This is not a Lean theorem or an
early-stop factoring lower bound. Keep the frozen experiment inconclusive.

[Review](findings/H006-independent-review.md),
[disposition](findings/H006-disposition.md). tasks-H006.json is complete.
H011 completed the revised inverse-interval reporting question below;
few possible outputs do not imply cheap enumeration.

## H007–H011: subsequent focused work

H007 completed a concrete scalar-normalized transfer-block construction and
33 exact checks. The coordinator accepted its restricted pole/nonunit
obstructions and cost accounting, with the factor-or-action scope clarified.
Its fast factor-return branch has known N^(1/4) scale; the different series
Newton revision retains dense index-sized storage. Close these fast-extractor
claims; a different coefficient algorithm remains open.
[Disposition](findings/H007-disposition.md); tasks-H007.json is complete.

H008's independent review accepts at most one normalized primitive irreducible
quadratic per embedding when 72*epsilon*H^4<1. The thin-window parameters
eventually satisfy this threshold. The d-row bound does not apply to all
reducibles: they can introduce many new bounded-height linear factors. The
review retains exact common-factor parity conditions, including odd dependency
cosets. Close the thin-root irreducible-population claim, not global resultants
or factoring. [Disposition](findings/H008-disposition.md),
[review](findings/H008-independent-review.md). tasks-H008.json is complete.

H009 is the parent's reduced-ring ECM audit. All 12 configurations completed;
all 684 later stages met the density threshold, rejecting sparse collapse on
the frozen sample. A characteristic-zero generic-density derivation is recorded
as awaiting independent review, not a universal finite-ring lower bound. It
does not establish a faster batch evaluator or a factoring performance claim.
[Finding](findings/H009-reduced-ring.md), [evidence](experiments/H009/result.json).

H010 completed and rejected its frozen dense-bucket cap at N=143, a=35, k=2:
an 11-variable bucket exceeds cap 10; its output factor has only 10 variables.
All 688 statuses remain: 2 completed, 1 rejected, 685 unstarted. The exact
network/cancellation audits passed. This is a finite representation/order
failure, not an asymptotic width lower bound. This case has only 16 input pairs
and can be computed cheaply by conditioning; general conditioning costs 4^k.
Reserve the route until a new large-prefix primitive is supplied.
[Disposition](findings/H010-disposition.md); tasks-H010.json is complete.

H011 supplies a correct affine-lattice reporter but forces Theta(R^(5/2))
explicit classes in the full box. Its sharp second-difference identity prevents
moving the affine formula to shallower classes. The full cost misses the
R^(6/5) target; small output size does not pay for root queries. All 61 frozen
arithmetic cases passed, with 16 modular outputs but no actual factor pairs.
This is a restricted implementation obstruction, not a factoring lower bound.
[Disposition](findings/H011-disposition.md); tasks-H011.json is complete.

## H012–H031: current follow-up mechanisms

H012 implements exact Gauss-generated reciprocal certificates and whole-cell
envelopes, independently cross-checked by quadratic inequalities. All 96 frozen
cases completed with full covers. At 64/128/256 bits, median selected interval
counts were 2/2/4 out of 11/22/43 cells. The finite continuation criterion passed;
the fixed K multiplier 16 may merely buy constant-factor reuse. No semiprime
promise, matched factoring benchmark, or asymptotic cover bound is asserted.
Source/protocol/result hashes are preserved and verified.
[Finding](findings/H012-certificate-reuse.md),
[evidence](experiments/H012/result.json). The first independent review completed:
9,727 certificates, 314,101 coverage decisions, Gauss reconstruction, optimal
cover counts and all registered edge cases passed. All six original/audit
artifact hashes match. The finite result remains a pass of its original screen.

That [review](findings/H012-independent-review.md) also derives a new
Omega(phi(m)*n) full-range per-residue cover obstruction for infinitely many
actual semiprimes under the exact modulus rule, affecting a positive fraction
of unit residues. Axis certificates really have broad low-scale coverage;
the proof instead counts hard residue/scale pairs in an interior band. This
new proof has **passed a second independent review**, including the unit-slope
average, uniform error terms, Brun–Titchmarsh transfer and exact input scope.
The original short-interval source supports constant 4; no repair is needed.
Close the stated full-real-range per-residue compression premise. It does not
bound cross-residue sharing, integer-only coverage, adaptive search, distinct
modular values or factoring generally. [Disposition](findings/H012-disposition.md),
[second review](findings/H012-obstruction-review.md); tasks-H012.json is complete.

The separate [Lean note](findings/H012-formal-invariant.md) records five checked
algebraic theorems: integer evaluation, quotient existence under coprimality,
recovery, its converse for nonzero p, and a nonzero recovery polynomial. These
formalize existing algebra; they neither refine Python nor bound cover/search
cost. The quotient premise is not an arbitrary modular exponent collision.

H013's count poly(d)*(H³*N^(-6/(5d²))+H²), eta=2/5 full-scan model rejection,
and full-height resultant-1 example passed independent review. The coordinator
also checked the reviewer's analytic extension: all eta in [0,1] are excluded
at c<=2 in the same conditional population/smoothness relaxation. Close that
full-scan model. This is not a smooth-survivor or factoring lower bound.
[Disposition](findings/H013-disposition.md),
[review](findings/H013-independent-review.md); tasks-H013.json is complete.

H014 tests a concrete changed generator: coefficient lines
g=a*(X-1)²+beta*X+gamma, exact univariate resultants, real-root isolation of
the two threshold polynomials, and enumeration of accepted integers only.
The proposer supplied a mathematical construction and exact stdlib prototype
at H²*poly(n)+S_all*poly(n), including candidates later rejected by filters.
Its single preregistered validation passed all 47 cases in 3.09 seconds, with
0 failures, timeouts or unstarted cases. These are finite correctness checks,
not density evidence; the six recorded output hashes match. The construction,
explicit polynomial bit envelope, boundary handling and model inequalities are
now accepted after independent review. The review's additional arithmetic/access
ledger supports the conservative Z^30 finite-multitape realization, not a
CPython runtime theorem or Lean refinement. [Report](findings/H014-resultant-enumerator.md),
[evidence](findings/H014-enumerator-results.json),
[disposition](findings/H014-disposition.md); tasks-H014.json is complete.

Under the unchanged joint-smoothness model, eta=.4 still requires
c>=(1024/135)^(1/3), worse than the cited GNFS constants even with the changed
enumeration. At eta=.1, a0=.765, b0=.945, delta=2.1 give upper-population
exponent s=18491/9800 and a strict optimistic envelope 1.89. This is an
inequality witness only: neither actual useful supply nor the assumed joint
law, rank, square roots or proper splitting is established. Naive S*B trial
division raises its sufficient cost envelope to about 2.832; that is not a
lower bound on all smoothness algorithms. H016 separately evaluates batching.

H015 is a distinct parent screen of geometric batching for the deterministic
certificate collision stage. Whole-cell envelope bounds give |u|,|t|=O(sqrt(m)).
A fixed (u,t,v mod m²) family serves only O(sqrt(m)) unit residues. A proposed
stronger extension counts distinct t even after arbitrary u/v merging, then
uses giant-exponent bands near Nt to show exponentially many short runs or
large padding at the actual stride m². Both arguments **passed independent
review** with explicit thresholds and the sharper bridging cutoff
1+ceil((N-98H)/m²). Close polynomially many short literal-exponent runs under
the stated common-whole-cell obligation. They concern literal grouping, not
equal modular values after order identifications, other strides, or every
product algorithm; collectively processing many short runs remains open.
[Initial bound](findings/H015-geometric-family-bound.md),
[short-run extension](findings/H015-short-block-extension.md).
No finite experiment or new Lean proof was needed for these derivations.
[Disposition](findings/H015-disposition.md),
[review](findings/H015-independent-review.md); tasks-H015.json is complete.

H016's [construction](findings/H016-batch-smoothness.md) and
[independent review](findings/H016-independent-review.md) are complete.
Full integer prime-exponent recovery costs (B+S)*poly(n) under polynomial
scalar, payload, log B and log S widths. Restricted good-prime ideal
labels/valuations cost expected S*poly(n), or deterministic (B²+S)*poly(n)
with paid root-table joins. Sampling includes both independently uniform
coefficients of aX+b. Memory is working scratch; retained outputs are additional.
Discarding norms meeting disc(f) has unquantified supply loss. Characters,
rank, square roots and proper splitting remain distinct.
[Disposition](findings/H016-disposition.md); tasks-H016.json is complete.

H017's [conditional supply derivation](findings/H017-resultant-tail-supply.md)
passed [independent review](findings/H017-independent-review.md). Separated
normalized root triples control quadratic coefficients. An exact integer
inequality using certified rational root disks bounds primitive irreducible
tail members by (h_*-1)(2h_*-1)²+k. Under its stated uniform geometry, the
worst permitted large-root fraction gives primitive exponent <=1.521508,
below the modeled required 1.881197; reducibles separately have exponent
<=1.53. These are conditional counts, not an all-input geometry or randomized
field-selection escape theorem. The reviewer passed 30/30 preregistered
arithmetic checks; no root-geometry sample was run in H017.
[Disposition](findings/H017-disposition.md); tasks-H017.json is complete.

H018's [corrected derivation](findings/H018-degree-envelope.md) passed
[independent review](findings/H018-independent-review.md). Its fixed-r
upper-population relaxation has exact optimum
c_*³=64(r-1)[(r+1)+(r-1)eta]/(9r²), increasing in r. The linear r=2,
eta=.8 witness a=1,b=.95,delta=1.4 gives optimistic envelope 1.90.
This is no useful-supply theorem or algorithmic bound. A stronger uniform
homogeneity-based lattice count would close that apparent advantage, but
the count remains unproved. The parent corrected the exact 1.90 comparison
and specified the unfloored real threshold, retaining the original reviewed
bytes in H018-submitted-draft.md. No implementation, experiment or new Lean
theorem. [Disposition](findings/H018-disposition.md); tasks-H018.json complete.

H019's [finding](findings/H019-root-certificate-screen.md) retains the one
frozen trial: controls 5/5, research one pass and three unknowns. Its
[independent review](findings/H019-independent-review.md) accepts the finite
implementation and degree-52 primitive-irreducible upper count. A separate
exact replay verified all nine outcomes, 115 research disks and all four count
comparisons. The both-largest criterion remains unmet, so the experiment is
INCONCLUSIVE. The count is not an all-output bound, field certificate,
asymptotic theorem or factorization result. All original/review hashes match;
shared project checks passed after handoff. No revision required.
[Disposition](findings/H019-disposition.md); tasks-H019.json is complete.

H020's [derivation](findings/H020-linear-tail-supply.md) and
[independent review](findings/H020-independent-review.md) are complete.
Retaining x^r in the large-root estimate yields an exact dyadic containing
count. Under its geometry assumptions the primitive exponent is <=9/5,
below the unchanged witness's required 15101/7980. It includes the permitted
ordinary-base large-root fraction 25/49. The exact finite certificate and
polynomial-bit construction passed review without corrections. No experiment
was run, and useful-yield laws, uniform geometry, all-output costs and proper
factor extraction remain distinct. [Disposition](findings/H020-disposition.md);
tasks-H020.json is complete.

H021's [construction](findings/H021-structured-lattice-generator.md) supplies
exact minimum, enumeration, counting and sampling algorithms for the original
diagonal-plus-one-row objective. It passed independent review after a localized
optimizer-recovery correction; original bytes are preserved. Costs include
rational logs, coefficient magnitudes, count bits, outputs, precision refinement
and unit relation processing. This is a standard DP, with useful smoothness
and proper splitting unresolved. No implementation or finite run.
[Disposition](findings/H021-disposition.md); tasks-H021.json is complete.

H022's [corrected report](findings/H022-stratified-linear-envelope.md) extends
H020 across threshold, height and norm strata with actual f-height gamma.
The fixed-stratum count and exact displayed relaxation c³=32(1+gamma)/9 passed
independent review. The coordinator checked and adopted the review's compact
uniform expected-work formulation and exact mesh-error inequality. Adaptive
selection needs its own strategy-valid yield law; ordinary average smoothness
is insufficient. No numerical experiment, geometry law or Lean theorem.
[Disposition](findings/H022-disposition.md); tasks-H022.json is complete.

H023's [report](findings/H023-cluster-escape.md) and
[parent intake](findings/H023-intake.md) passed independent review without
algebraic changes. Its geometry-free H022 counterexample is accepted;
the ordinary-base separation premise cannot hold for all these representations.
Its skewed/rotated/binomial mechanisms are classified against existing
special-form NFS. Collection constants are conditional models only.
[Disposition](findings/H023-disposition.md); tasks-H023.json is complete.

H024's [report](findings/H024-low-energy-population.md) passed review without
algebraic corrections. It gives E_star<40ell², model-qualified optimization
costs, O(ell)-bit accepted outputs and M_k(E)<=exp(11E^(1/3)). Probability
quantifiers were made explicit; no positive useful-density law is accepted.
H026 now rejects the exact universal supply statement named by its reviewer.
[Disposition](findings/H024-disposition.md); tasks-H024.json is complete.

H025's [report](findings/H025-small-residual-density.md) passed review after
replacing a broad “sublinear” description by the proved fixed power saving.
It counts inputs admitting small actual residuals from a fixed universe,
not smooth rows or successful splits. The dependency on H024's diagonal
count is now independently accepted. Higher energy and changed controlled
universes remain possible escapes with no useful selector supplied.
[Disposition](findings/H025-disposition.md); tasks-H025.json is complete.

H026's [proof](findings/H026-smooth-residual-supply.md) passed independent
review without mathematical corrections. Its exp(o(ell)) input count and
explicit balanced-semiprime comparison reject the exact fixed-base/weight/
cutoff universal smooth-supply lemma. This does not exclude changed generators
or establish a fixed-input conditional rarity law. Two scope clarifications
were applied and original evidence preserved. No experiment, code or Lean;
[disposition](findings/H026-disposition.md), tasks-H026.json is complete.

H027's completed [report](findings/H027-adaptive-generation.md) assesses a
smooth modular walk, exact power-of-two conditioning and quadratic CRT
generation. Literal conditioned outputs can be enormous; a modular variant
has short representations but unproved useful yield. The CRT card returns the
known quadratic-sieve model. Its scoped deductions passed independent review
after six clarifications and the paid sequential C4 access completion. The
literal-output ensemble falsifier is accepted only for its specified sampler;
no actual useful-yield theorem or new survivor is supplied. The original
submission is preserved; [disposition](findings/H027-disposition.md),
tasks-H027.json is complete. The coordinator's [prior-art check](findings/H027-root-entropy-prior-art.md)
confirms that its suggested root-entropy question is the existing gap in
Lee–Venkatesan section 7/Conjecture 7.82, including the multi-field extension.
A changed sampler or a new independence proof is required; adding the Jacobi
discriminator or reusing conditional kernel sampling is not a solution.

H028's completed [report](findings/H028-polynomial-sharing.md) reconstructs
Coppersmith's known balanced multi-field constant, separates amortized setup,
and assesses field-index processing and compatible shared columns. It claims
processing-only savings leave that restricted model optimum unchanged; naive
field-label cancellation is invalid, while a valid common-integer-column
construction returns N-sized norms. No new survivor or general lower bound.
Independent review accepted its mathematical core and scoped closures. The
coordinator adopted three repairs: attempted-index spans, discarded-record
costs, and strategy-valid expected supply/full cost. No new survivor.
[Disposition](findings/H028-disposition.md); tasks-H028.json is complete.
Original submission and review evidence are preserved.

H029's completed [report](findings/H029-power-cover-construction.md) checks the
parent's restricted same-base capacity bound and closes an explicit high-order
prime-menu certificate. Its second card uses known Lehman coverage with paid
small-factor preprocessing. The proposed positive square-difference leaves
are smaller than the surviving semiprime, enabling actual cheap visited Leaf.
Its supplied product scans Theta(M^(1/3)) rows. A uniform all-interval,
all-modulus RootProduct exponent below 1/5 would change the deterministic
comparison, but no such algorithm is supplied. This is the selected proof-only
question after review, not a new speedup. The original [parent calculation](findings/H029-intake.md)
and [construction intake](findings/H029-construction-intake.md) are preserved.
The mathematical core passed independent review, and the coordinator adopted
its local specification repairs. Root-gcd initialization and restoring all
original multiplicities are explicit; the uniform small-leaf proof is accepted.
[Disposition](findings/H029-disposition.md); tasks-H029.json is complete.
No new factoring bound, finite experiment, shared code or Lean change.

H030's [report](findings/H030-root-product-blocks.md) completes the exact
Newton-cubic realization selected in its [brief](hypotheses/H030.md). It specifies
rational Bernstein boundary certificates, recursive subdivision, denominator
clearing, and composite-ring polynomial products for arbitrary leaf intervals.
Its full bound remains M^(1/3)*poly(log M). The proposed obstruction derives
second differences in {-2,-1,0,1} on a long outer-root interval, limits exact
degree-D blocks to max(8,4D-6) positions, and forces Omega(M^(1/3)) explicit
cubic records. With e listed exceptions the proposed bound is L<=4D+9e+8;
its cost conclusion requires dense coefficient lists and explicit exceptions.
These scoped deductions passed independent review without algebraic repair.
Three clarifications specify weighted short-row counts, actual record traffic,
and separately materialized dense lists through actual degrees. They establish
no general RootProduct or factoring bound. The
[disposition](findings/H030-disposition.md) records acceptance and closure;
[original submission](findings/H030-submitted-draft.md), intake and manifests
remain preserved. tasks-H030.json is complete. No experiment, implementation
or Lean change was made; no new primitive is selected by the report.

H031's [report](findings/H031-coupled-field-roots.md) specifies adjacent
input-only rotations, a complete relation scan, separate good-ideal blocks,
joint rational parity and at most two actual field roots. For fixed retained
data it proposes success probability zero for a trivial productive character,
otherwise 2^(-c_t-1), where c_t is the actual-square subspace codimension.
The full law weights all field failures, early gcd successes and sampled
dependencies. No lower bound on useful mass is established. Its submitted
L_N[1/3,3+o(1)] trial bound charges large exact product coefficients, Lenstra
field-polynomial factorization and dense linear algebra; it supplies no
successful expected factoring bound or preserved best square-congruence cost.
The packet equality reduces to the existing global rational-square mechanism.
The [construction intake](findings/H031-construction-intake.md) records the
coordinator's provisional checks and explicit review obligations; the original
[organizing intake](findings/H031-intake.md) and identical
[submission](findings/H031-submitted-draft.md) are preserved. tasks-H031.json
records completed construction and independent review. Its corrected finite
trial, localized recovery, exact success identity and per-trial envelope are
accepted in [H031's disposition](findings/H031-disposition.md); useful mass is
still unproved. No finite experiment, code or Lean change accompanied that
acceptance, and the report selects no revised constructive question.

## Initial environment diagnostic H001

[Finding](findings/H001-initial.md): 156 attempts, including 126 composite
attempts with 122 verified successes and four Fermat event-budget failures.
The remaining 30 attempts were prime/0/1 controls outside the promise. Two seeds
are repeated trials, not extra distinct inputs. Favorable square/close-family
measurements provide no general complexity evidence.

Durable archive:
[H001-initial-run/report.md](findings/H001-initial-run/report.md), raw JSONL,
configuration, exact corpus, hypothesis/source snapshots and hashes. Original
research/runs scratch is not the durable archive. The default algorithms remain
the known trial-division, Fermat and rho baselines.

H002 remains an unregistered broad square-relation placeholder, not a solver.
The public holdout config is not blind evaluation and has not been used here.

## Validation and remaining obligations

Latest ./scripts/check.sh passed all 12 Python tests, the source screen and the
pinned Lean build, including Factoring.Certificates. The new algebraic proofs
use standard propext, Classical.choice and Quot.sound as printed in Audit.lean;
there are no new user axioms or unchecked proof escapes. Closed reference
examples remain kernel checked. No new research mechanism is installed in the
shared solver, and no new complexity proof is asserted.

Still needed for a major result: executable useful primitive, matched baseline,
all-input correctness, uniform complete bit cost, success probability where
needed, and independent critical review. Machine-model refinement is required
before a formal complexity claim, but should not become an infrastructure
project in the absence of a surviving algorithm.

The original blog's polynomial factoring prediction and P=BQP conjecture are
separate. Failed representations do not disprove either existential claim, and
a fast factoring algorithm alone would not establish P=BQP.
