# W006 cyclotomic validation — review outcome

Date: 2026-10-08. **The conditional all-unit theorem and the sufficient
primality-certificate logic pass this independent mathematical audit. The
proposed fixed large instance is UNKNOWN under the authorized finite-base
protocol. It is not an established counterexample.**

The single execution found no certificate for 1610612737 in the five-base
menu; 3221225473 certified prime at base 5. Consequently none of the four
folded-vector cases ran. No replacement target, extra primality method,
rerun, huge central binomial, tiny 48-case corpus, factoring benchmark,
shared source edit, registry edit, Lean edit, commit or publication occurred.
Verified new end-to-end factoring improvement: **NONE**.

## Review disposition and exact mathematical scope

**Promising as an analytic obstruction; inconclusive as the proposed fixed
certificate instance.** The scoped coefficient-gcd operation is obstructed
whenever primes p,q=2p-1 and a power of two L>=2 satisfy p=1 mod L,
p>L-1 and q>(L-1)^phi(L). All folded coefficients are then units modulo pq.
This does not prove eligible prime pairs exist at every size, reject every
polylogarithmic degree/menu, or imply factoring hardness. The known relation
between the factors would itself make factoring easy by an integer square root.

The complete proof audit was written and frozen **before execution** in
[the symbolic audit](W006-cyclotomic-validation-proof.md). Its conclusions are:

- **p exponent:** pq-1=(p-1)(2p+1) exactly. The exceptional value at -1 is
  zero, since the exponent is positive. All other L-th roots evaluate to 1.
- **Inverse transform:** the coefficient vector modulo p is
  f_0=(L-1)/L and f_j=(-1)^(j+1)/L for j>0. The inverse q transform is
  L*f_j=sum_r F(omega^r)omega^(-jr), with the r=L/2 term zero.
  Distinct roots and invertibility of L hold in both fields.
- **Power-of-two parity:** with d=L/2, Phi_L(T)=T^d+1 yields
  Z[zeta]/(1-zeta)=F_2. Each of the L-1 signed terms reduces to 1.
  Thus C_j is a nonzero algebraic integer, including at L=2.
- **Prime and norm implication:** substituting zeta->omega defines a
  surjection to F_q with kernel (q,zeta-omega). If f_j vanishes, that
  prime contains C_j. The integer determinant defining its norm is then
  zero modulo q. Section 3 gives a direct matrix proof, so no unstated
  prime-splitting theorem is needed.
- **Strictness:** 0<|Norm(C_j)|<q follows from nonzeroness and
  |Norm(C_j)|<=(L-1)^d<q. This contradicts q dividing that norm.
  Nonzeroness alone would not suffice. The upper norm estimate is weak;
  the assumed inequality against q must be strict for this proof.
  Also p>=L+1 already follows from p=1 mod L, so p>L-1 is sufficient
  and redundant, not an omitted restriction.
- **Certificate:** if gcd(a,t)=1 and a^(3*2^(e-1))=-1 mod t, every prime
  divisor r has ord_r(a) with 2-adic part exactly 2^e. Hence
  r>=2^e+1>sqrt(t), contradicting compositeness. Repeated prime factors
  create no exception. The size condition was tested using integer squares.

The audit also checks the exact central selector, its v_p=1 and v_q=0,
the original L=2 and L=4 formulas, and the original two-reflection identities.
The reflection observation has a short complete denominator argument:
a final one-sided multiplier has denominator both dividing N and coprime
to N, so is integral; norm one and orthogonality force a pure signed unit.
This covers repeated primes and avoids an unsupported claim about arbitrary
two-sided rotations. No later reflection parameterization or separate agent
experiment is promoted by this report.

The full-work statement supported here is the elementary O(L^2 log N)
modular multiply-add count and O(L log N) candidate working bits for dense
folding, excluding retained traces. With classical arithmetic and
log L=O(log N), a conservative bit upper bound is O(L^2(log N)^3), plus
gcds. There is no success guarantee or factoring comparison. The exact
central coefficient has Theta(N) bits; its existence is not an acquisition
algorithm.

## Every fixed-target outcome

Exact hypotheses checked for the two target cases:

- 1610612737=3*2^29+1; 2^29=536870912 and
  (2^29)^2=288230376151711744>1610612737.
  Powering exponent: 805306368.
- 3221225473=3*2^30+1; 2^30=1073741824 and
  (2^30)^2=1152921504606846976>3221225473.
  Powering exponent: 1610612736.

All tested base gcds were 1. No proper base gcd was obtained.

| Target | Base | Half-exponent residue | Recorded modular multiplies | Frozen-protocol result |
|---:|---:|---:|---:|---|
| 1610612737 | 2 | 210670523 | 31 | Failed witness |
| 1610612737 | 3 | 88851999 | 31 | Failed witness |
| 1610612737 | 5 | 1609169494 | 31 | Failed witness |
| 1610612737 | 7 | 1194053625 | 31 | Failed witness |
| 1610612737 | 11 | 1124940576 | 31 | Failed witness |
| 3221225473 | 2 | 1 | 32 | Failed witness |
| 3221225473 | 3 | 1 | 32 | Failed witness |
| 3221225473 | 5 | 3221225472 | 32 | PRIME_CERTIFIED |

The first target has **NO_WITNESS / UNKNOWN**. This is a conservative
protocol status, not a probable-prime assertion. The frozen implementation
only labels proper checked base gcds as composite evidence; it does not
apply an additional compositeness criterion to failed-witness residues.
The second target's first witness is **5**; bases 7 and 11 were intentionally
not tested because the required first-certificate stopping rule fired.
No fixed-base completeness claim is used.

Combined theorem instance: **UNKNOWN**. The evaluator did not form N and
did not enter the vector or instance-inequality evaluation branch:

| Degree L | Status | Reason |
|---:|---|---|
| 2 | UNKNOWN, unstarted | Both target certificates required |
| 4 | UNKNOWN, unstarted | Both target certificates required |
| 8 | UNKNOWN, unstarted | Both target certificates required |
| 16 | UNKNOWN, unstarted | Both target certificates required |

Thus there are no numeric vector coefficients, coefficient gcds or a
measured all-unit failure instance from this run. They must not be inferred
from the conditional theorem. These four unstarted cases remain explicit
in the six-case protocol record. There were no censored target cases.

## Budget and evidence accounting

| Case | Events | Max input/modulus bits | Max unreduced bits | Cold seconds | Peak traced bytes | Binary trace bytes |
|---|---:|---:|---:|---:|---:|---:|
| Target 1 | 155 | 31 | 62 | 0.063896 | 5113051 | 4960 |
| Target 2 | 96 | 32 | 64 | 0.061314 | 5110526 | 3072 |

All target cases stayed below 1 second, 20,000 modular events, soft 32 MiB
traced allocation and 1 MiB evidence. Recorded whole-run elapsed time was
0.167048 seconds, including runner setup/hash checks and case orchestration
through the final report assembly. Final outcomes serialization followed
inside the external 60-second timeout, which exited successfully. Parent
peak traced allocation was 5344052 bytes. Retained evidence before outcomes
was 1809359 bytes, below 16 MiB; final delivery size is also recorded in
the delivery manifest. This is not a factoring performance comparison.

Each little-endian `<QQQQ` binary record contains the full reduced operands
x,y,acc and output of `(x*y+acc)%t`. Scalar powering uses acc=0. These are
complete operation records, including squarings, with no enormous operands.
The exact source and exponent determine the operation order. Metadata gives
event intervals for every base, maxima before and after modular reduction,
and SHA-256 identities. Gcd internals and ordinary setup integer operations
are timed but not classified as modular multiply-add events. Tracemalloc
covers Python allocations, not OS RSS or all native allocations.

The candidate source takes only N,L and generates explicit dense arithmetic
requests. The instrumentation supplies only their paid multiply-add results.
No factors, prime-order data, family label or coefficient oracle enter that
boundary. In this execution the candidate was correctly never invoked.

Pre-run manifest SHA-256:

    ab81abf612b94a7994fe94303f8bc4aef605a2d74c6b6870ee3456169ad48060

Artifacts:

- [Frozen manifest](W006-cyclotomic-validation-freeze.json),
  [protocol](W006-cyclotomic-validation-protocol.md),
  [symbolic audit](W006-cyclotomic-validation-proof.md).
- [Runner](W006-cyclotomic-validation-screen.py) and
  [candidate](W006-cyclotomic-validation-candidate.py).
- [Single execution marker](W006-cyclotomic-validation-execution-started.json),
  [execution log](W006-cyclotomic-validation-execution.log),
  [complete outcomes](W006-cyclotomic-validation-outcomes.json).
- [Target 1 metadata](W006-cyclotomic-validation-case-target-1.json) and
  [binary transcript](W006-cyclotomic-validation-case-target-1.bin);
  [target 2 metadata](W006-cyclotomic-validation-case-target-2.json) and
  [binary transcript](W006-cyclotomic-validation-case-target-2.bin).
- [Saved-evidence audit](W006-cyclotomic-validation-evidence-audit.json):
  all 24 frozen file identities, trace lengths/hashes, reduced operand ranges,
  base intervals and saved final residues agree. This was inspection of
  recorded evidence, not a rerun or new primality test.
- [Project check log](W006-cyclotomic-validation-check.log):
  `scripts/check.sh` exited 0 after scratch code. All 12 Python tests,
  Lean source screen, 7-job build and `Audit.lean` completed successfully.
  These existing project checks do not formally prove the new theorem or
  exercise the skipped large vectors.

## Prior art and the computation still needed

The bounded primary-source audit, exact read scopes and local PDF snapshots
are recorded in section 7 of the frozen proof. Granville supplies classical
binomial valuation/digit background and known-prime-power evaluation;
Sze's Theorem 1.1 supplies the established Proth certificate; Lam–Leung
supply characteristic-zero vanishing-weight theory and a separate finite-field
study. The power-of-two parity special case and norm transfer were also
proved directly here. No exact W006 theorem attribution, exhaustive survey,
novelty assertion, or algorithmic speedup is claimed.

The exact failed assumption is that cyclic aliasing retains the central
coefficient's zero modulo p. Under the conditional obstruction, its residue
class instead has nonzero aggregate value (L-1)/L modulo p when m=0 mod L;
the other aliases erase the selector. This is an aggregate symbolic statement,
not an unauthorized computation of the enormous terms or of the skipped vector.

A materially different next construction must preserve the middle
coefficient's information: specify a block-isolating state or equivalent
computable quantity, with charged dimension, modulus precision, arithmetic,
and useful-output guarantee. Naming a Hasse coefficient, trace or recurrence
without that computation does not meet the obligation. A different folding
degree could also lie outside this theorem; no such search was authorized or
performed. The fixed target/menu is closed for this review, with all outcomes
retained and no replacement requested or attempted.
