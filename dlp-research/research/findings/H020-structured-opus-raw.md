Provider: claudeAgent / claude-opus-5-5
TaskId: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h020-structured-batching-opus-20261008-r1
Status: completed; no pending children. Raw report NOT endorsed. Root flags unsupported displacement/functional claims, value-support versus multiset-degree confusion and broad complexity exclusions. Independent review requested.

## H020 independent exploration — final report (read-only sub-agent)

Context digested: `RESEARCH_LOOP.md`, `RESEARCH_TEAM.md`, `research/STATE.md`, and the accepted dispositions `H019-single-query-resultant.md`, `H019-detector-disposition.md`, `H017-SP3-disposition.md`, `H017-SP3-detector-screen.md`. I did **not** read the other live H020 proposals. No edits, runs, children, commits, or targeting. Baseline = classical square-root reference (known automorphism constants, all setup/memory/failure/verification charged); improvement **NONE**.

**The barrier I am trying to get around, stated precisely.** The single-query resultant computes `D(α)=Res_X(H_A,R_α)=∏_{i,j}S3(u_i,v_j,α)` at one `α` in soft-O(n). As a function of `α`, `D` is a polynomial of degree `2ab≈2n²` whose roots are exactly the pair-sum abscissae `x(A_i±B_j)`. Detecting whether any of `r` third-list values is a root is multipoint evaluation of a degree-n² polynomial — and for *generic* lists `|A+B|=Θ(n²)`, so `D` genuinely has `n²` coefficients. The quotient-ring route (resultant over `Fp[Z]/C`, `deg C=r`) is soft-O(n·r)=n² for the same reason. So any escape must exploit a **real EC-specific structure** that makes the pair-sum set *not* behave like `n²` arbitrary values. Below I give four concrete mechanisms, each with an actual EC bridge, and I separate "missing proof" from "missing mechanism."

---

### Card 1 — Cauchy/displacement structure of the pair-sum matrix (EC bridge is real; the detection primitive is the missing mechanism)

**Exact operation.** For a target `w`, form the `a×b` matrix `M(w)_{ij}=S3(u_i,v_j,w)/(u_i−v_j)² = (w−x(A_i+B_j))(w−x(A_i−B_j))`. Using the root form of `S3` in its third slot, the pair-sum *coordinate* matrix is
`x(A_i+B_j)+x(A_i−B_j)=2[(u_i+v_j)(u_iv_j+a)+2b]/(u_i−v_j)²`, `x(A_i+B_j)·x(A_i−B_j)=[(u_iv_j−a)²−4b(u_i+v_j)]/(u_i−v_j)²`. The denominator `u_i−v_j` is **exactly Cauchy structure**; the numerators are low-bidegree. Hence the generating matrices are Cauchy-like of bounded displacement rank (Hadamard products/squares of the rank-1 Cauchy kernel `1/(u_i−v_j)`). Recovery on a detected zero entry: one-list scan + A-dictionary → labels, signs, target-coefficient check, scalar verification (soft-O(n)).

**Positive mathematical reason.** Displacement-structured (Cauchy-like) matrices support matrix-vector multiply, triangular solve, and generator manipulation in soft-O(n·δ) with `δ` the displacement rank (Pan; Gohberg–Olshevsky), versus `n²` dense. The EC addition law *forces* this structure through the `u−v` denominator — this is genuinely curve-specific, not generic.

**Prior-art distinction.** Structured-matrix literature (V. Pan, *Structured Matrices and Polynomials*; Gohberg–Olshevsky, *Complexity of multiplication with vectors for structured matrices*, Linear Algebra Appl. 1994) accelerates linear-algebra functionals. No source I know converts low displacement rank into **sublinear detection of a prescribed-value (zero) entry**; H019/H017 dispositions only reached dense `n²` materialization and rank-bound counting, not this structured-linear-algebra framing. Access: these are standard references from knowledge; cheapest verification is paper cost-accounting, not a fetch.

**Full costs/setup/memory/failures.** Generators: soft-O(n) per target. Any linear functional of `M(w)` (traces, `∑ 1/(w−S_{ij})`, power sums): soft-O(n). Memory soft-O(n). Failure/the gap: a *zero entry* is invisible to matrix-vector products and to low-degree power sums (a single zero among `n²` entries perturbs `∑_{ij}(w−S_{ij})^k` by O(1) out of O(n²) — undetectable without Ω(n²) precision). Multi-target: each `w` is soft-O(n) for functionals, so `r=n` functional-queries = `n²` — no gain *unless* a single structured primitive handles all `r` at once.

**Unsupported assumption.** That "existence of a zero entry" in a Cauchy-like matrix is computable in soft-O(n·δ). It is not a known structured-matrix primitive.

**Cheapest decisive falsifier.** Produce (or cite) a structured-matrix algorithm that, given displacement generators of an `n×n` Cauchy-like matrix, decides whether any entry equals a prescribed value in `o(n²)` field ops — *or* reduce exact zero-entry detection to a functional provably not accelerated by displacement structure (e.g., show it needs Ω(n²) evaluations of the only cheap functionals). A one-page analysis settles it; this is **missing mechanism**, not missing proof.

---

### Card 2 — √élu / Bostan–Gaudry–Schost baby-step/giant-step structured products on group-AP lists (EC bridge real; gain honestly lands at √q)

**Exact operation.** Choose structured lists: `A={a_0+iR}`, `B={b_0+jS}` (arithmetic progressions *in the group*, i.e. elliptic nets). Then `x(a_0+iR)` satisfies the elliptic-divisibility/elliptic-net recurrence, and the per-row product `∏_j S3(u_i, x(b_0+jS), α)` is a product of a fixed polynomial over an AP of EC points. The Bernstein–De Feo–Leroux–Smith √élu construction (arXiv:2003.10118, already in-repo — the same paper H019 used for the single-query identity) computes exactly such products `∏_{s∈AP} h(x(s))` in soft-O(√(#terms)) via a baby-step/giant-step resultant. Recovery as in Card 1.

**Positive mathematical reason.** √élu/BGS turn a length-`N` product over an AP of EC points into soft-O(√N) field work (Bostan–Gaudry–Schost, *Linear recurrences with polynomial coefficients…*, SIAM J. Comput. 2007; BDLS 2020). The AP/elliptic-net recurrence is the curve-specific structure that licenses the √-reduction.

**Prior-art distinction.** BGS/√élu are used for isogeny evaluation and point counting, never (to my knowledge) as a **triple-list ECDLP detector**. H019's resultant disposition used BDLS only for the *single-input* identity and explicitly noted "n queries still cost soft-O(n²)"; it did not analyze AP lists where √élu could also batch across queries. H013 raw mentions √élu/BGS as "equals MITM, loses polylog to BSGS" but did not work the *triple-AP* joint cost.

**Full costs/setup/memory/failures.** Single query with both lists AP: plausibly soft-O(√(ab))=soft-O(n) (already matched). The real test is whether a third AP list `L3` lets the `r` queries `D(w_1..w_r)` share the baby/giant tables for soft-O(n·√r) or soft-O(√(nr)). **Honest expectation:** triple-AP structure reconstructs BSGS, so the complete-work optimum lands at √q — *no improvement* — because the three APs together just enumerate the group. Memory soft-O(√·) tables; setup = elliptic-net initialization, charged. Failures: exceptional/duplicate abscissae, O-branch, verification — all charged.

**Unsupported assumption.** That the √-saving compounds across the *three* AP directions to beat `n^{3/2}` rather than saturating at √q. I believe it saturates; the card's value is a *clean, worked* cost that either confirms √q or exposes a genuine compounding.

**Cheapest decisive falsifier.** A paper cost table for triple-AP √élu detection as a function of `(a,b,r)` optimized over the full range: if the minimum exceeds `c·√q` for all splits, closed (no gain, EC bridge notwithstanding); if any split gives `o(√q)` with recovery charged, that is a real signal warranting one frozen experiment.

---

### Card 3 — Modular composition (Kedlaya–Umans) as the join operator (EC bridge is a candidate; degree-n presentation of the n² image is the missing mechanism)

**Exact operation.** We want to detect `A_i+B_j=−C_k`. The map "B-point ↦ x-coordinate of A-list sums" is an algebraic correspondence from the addition morphism `E×E→E`. If (hypothetically) the A-list image under `+B` could be presented as a *single* degree-n polynomial `g` and the target set as `h`, then `gcd`/composition `f(g) mod h` via Kedlaya–Umans runs in `n^{1+o(1)}`. Recovery via the composition's witness.

**Positive mathematical reason.** Kedlaya–Umans modular composition (*Fast polynomial factorization and modular composition*, SIAM J. Comput. 2011) computes `f(g) mod h` for degree-n polynomials in `n^{1+o(1)}` — strictly below `n^{3/2}`. If the EC join could be cast in that shape, it would break the quadratic wall.

**Prior-art distinction.** KU composition underlies modern factorization/point-counting; it has not been applied to the ECDLP pair-join. H019's quotient-ring analysis used plain ring arithmetic (soft-O(n·r)), *not* KU composition.

**Full costs/failures and the honest gap.** The intermediate object — the pair-sum set — has `Θ(n²)` distinct elements for generic lists, so there is **no known degree-n polynomial presenting `A+B`**; the three inputs KU needs are not available. This is the same wall as Card 1/2 viewed through composition.

**Unsupported assumption.** Existence of a soft-O(n)-size (degree-n) algebraic presentation of the restricted addition image `A+B`. Generic sumset size `Θ(n²)` contradicts it *unless* the lists carry additive structure (which routes back to Card 2's AP case).

**Cheapest decisive falsifier.** Instantiate KU with the *actual* intermediate degree and input format for the pair-join: either exhibit a degree-O(n) presentation of `A+B` with recoverable labels (would be a breakthrough), or show the required `g` has degree `Θ(n²)` so KU costs `n²`. One-page dimensional check — **missing mechanism** (a compression), not missing proof.

---

### Card 4 — Transposition + output-sensitive early-abort (screened; documents the exact barrier shape and the one thing that reopens it)

**Exact operation.** For `r` targets, instead of `r` independent resultant runs, treat `α↦D(α)` as one linear map (coefficients → values) and apply Tellegen's transposition principle, with early abort the instant any remainder-tree node vanishes (a zero = a detected relation, so we never finish the full product).

**Positive mathematical reason (and why it fails).** Transposition guarantees the transposed map costs the same as the forward map — but both are dominated by *producing* `D`, and `D` has `Θ(n²)` coefficients irreducibly for generic lists. Early-abort helps only when a relation *exists and is found early*; for the decision "no relation," it still reads `Θ(n²)`. So transposition/early-abort **do not** beat the wall; I present this explicitly so root can retire the "transposition will save it" intuition with a precise reason.

**Prior-art distinction.** Tellegen/transposition (Bostan–Lecerf–Schost, *Tellegen's principle into practice*, ISSAC 2003) is standard; no EC-join application reduces below the output size.

**The one reopener (distinguishes missing proof from missing mechanism).** The entire wall rests on `|A+B|=Θ(n²)`. A non-generic list family with `|A+B|≪n²` *and* efficiently recoverable labels would collapse `deg D` and make transposition/composition/multipoint all sublinear. AP lists (Card 2) are the canonical such family but saturate at √q. The open, non-obvious question is whether any *other* structured family has `|A+B|=o(n²)` with labels recoverable from x-coordinates alone.

**Cheapest decisive falsifier/validator.** Characterize list families with sub-quadratic sumset and coordinate-recoverable labels: by Freiman-type structure theory, small-sumset sets are (generalized) progressions — i.e., essentially Card 2 — strongly suggesting √q is the floor; a short additive-combinatorics argument on `E`'s cyclic group either confirms this (closing Cards 1–4 jointly at √q) or names a new family (reopening everything).

---

### Bottom line

All four mechanisms share **one** honest status: the EC addition law supplies *genuine* structure (Cauchy/displacement in Card 1; elliptic-net/√élu in Card 2; an addition correspondence in Card 3), but every route to sub-`n^{3/2}`/sub-√q detection needs the pair-sum multiset to be *small or structured in the value domain*, and generically it is `Θ(n²)` distinct values. The gap is a **missing mechanism** — a structured zero-entry/membership primitive (Card 1) or a sub-quadratic coordinate-recoverable sumset family (Cards 2/4) — not a missing proof of a known theorem. I did **not** convert the `n²` output size into a universal lower bound; Cards 1 and 4's reopeners are explicitly the way out, and Card 2 is the concrete, worth-costing lead (triple-AP √élu) whose expected but unproven saturation at √q is the single cheapest thing to settle on paper next. No experiment is justified yet; verified improvement remains **NONE**.

(Delivered as text for root to integrate; no files written, per the read-only brief.)
