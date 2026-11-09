You are the independent constructive researcher for Lens A ONLY in the frozen W002 brief below. Work only in /home/mj-kang/Documents/Dev/math/factoring-research. Your exclusive report is research/findings/W002-paired-residual-products.md; only adjacent supporting artifacts matching W002-residual-* are yours. Do not change shared files, read sibling W002 drafts, or recursively delegate. This is a research task, not a self-review.

Current authoritative handoff: H030 and H031 independent reviews are complete and the coordinator accepted their scoped corrected deductions; both fail to establish a new complete factoring bound. Read their current dispositions. research/STATE.md may briefly lag while the parent updates it; H031 is NOT live and does NOT need another duplicate review. A new mathematical deduction in your report remains UNACCEPTED pending independent review. Preserve any retrieved primary source and all input identities needed to reproduce your reasoning. Finish with the strongest supported conclusion, exact limitation, and at most one decisive preregistered next proof/test. No numerical experiment or implementation is authorized in this symbolic wave.

Frozen brief SHA-256: 5f34c276110ba4ad79781b16b4a86d7ea3860671d168939aca9c399b0480f723.

# W002 — Constructive reseeding after the H030/H031 closures

2026-10-08. **Analytic research wave; no accepted algorithmic improvement.**
Verified COMPLETE classical factoring complexity improvement: **NONE**.

The user authorizes continued T3 subagents toward lower full classical factoring
complexity, with experiments and focused Lean proofs only when a concrete
candidate justifies them. H027-H031 reviews are complete, their scoped results
accepted after local repairs, and their original evidence preserved. No current
candidate supplies a new complete factoring bound. This wave selects three
different computations, not larger sweeps of the rejected implementations.

## Shared rules and comparison

Read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, STATE, the W001 synthesis and the relevant accepted
dispositions. Reopen only the exact scopes assigned below. Do not repeat prior
reviews or convert representation failures into factoring lower bounds.

Each researcher considers concrete alternatives within its assigned lens, then
develops one explicit N-only realization. Give a finite algorithm, constructed
parameters, all costs and the exact missing mathematical statement. Prefer a
decisive proof or falsifier over a list of conjectured oracles. If the only
available realization is known or fails, identify the first actual obstruction
and close only that realization. A symbolic expression for the desired output
is not a way to compute it. Do not force a new task merely to fill a quota.

Primary-source checking is required before novelty/comparison claims. Distinguish
rigorous complete factoring, conditional/heuristic NFS, deterministic power
bounds and special-input or smaller-factor results. N^(1/6) remains exponential
in input bit length and does not beat heuristic GNFS asymptotically. ECM
L_p[1/2] constant improvements do not beat general NFS's L_N[1/3] exponent.
All claimed conditional consequences retain the actual input/distribution laws.

Full costs include input-only setup, attempted/rejected data, operand widths,
memory and access, preprocessing, decoding, every root or inverse, intermediate
representations, randomness, success failures, factor recovery and restarts.
No factor, order, prime-counting, relation-density or productive-root oracle.
Cheap verification of a witness does not make finding it cheap.

No finite mathematical experiment, numerical sweep, benchmark, implementation,
Lean change, package, recursive delegation, outside-project write, commit,
publication or scheduler in this wave. Symbolic derivation and primary-source
inspection/archiving only. If a test is essential, deliver its preregistration
proposal for later execution. Parent owns shared files and all acceptance.
Each child owns only its report and its named adjacent evidence prefix.
New major deductions require independent review before acceptance.

## Lens A: factoring-specific paired residual products

Exclusive report: research/findings/W002-paired-residual-products.md.
Exclusive supporting prefix: W002-residual-*.

Read H029's corrected construction/disposition, H030's corrected report and
disposition, and H004's accepted reduction. H030 closes exact consecutive
polynomial representations over Q; it does not bound a direct modular product.

Investigate one actual algorithm exploiting the divisor-of-input promise and
the paired identity. On the H029 semiprime remainder M=pq, p>K0 from its paid
small-factor stage, use the unchanged (j,k,t) descriptor, x=ceil(sqrt(4kM))+t,
y=floor(sqrt(x^2-4kM)), and e=x^2-4kM-y^2. For d|M,
(x-y)(x+y)=e mod d. Unlike H030, this lens may return a verified proper factor
of its assigned d when a nonunit is encountered, instead of continuing an
arbitrary-modulus residue computation. This is a changed interface requiring
its own reduction/cost proof, not an implementation of all-modulus RootProduct.

Select a concrete way to compute or search paired residual products without
building all Theta(M^(1/3)) roots or a dense exact-polynomial block cover.
Intervals must retain original row identities. If a paired product is zero,
paid recovery may recompute that row and split through x-y,x+y; prove it,
including trivial/full gcd branches and restoring original multiplicities.
Do not treat zero residuals as known in advance or unlocatable certificates.
Price all once-per-input data, queries, nonunits and failures. Target a complete
deterministic exponent below 1/5, ideally 1/6, with the known N0^(1/6)
preprocessing included. A d|M-only result needs no arbitrary-d extension but
must suffice for the actual factorer. Check Harvey/Hittmeir prior art so a
reformulation of the existing Lehman search is not called a new algorithm.

## Lens B: an input-dependent relation universe with charged generation

Exclusive report: research/findings/W002-adaptive-relation-universe.md.
Exclusive supporting prefix: W002-adaptive-*.

Read H021/H024-H027 dispositions and the H028/H031 corrected reports/dispositions
as relevant. H026 excludes the specified common aligned prime/weight/low-energy
universe on most inputs of an explicit semiprime ensemble. It does not exclude
N-dependent bases or a genuinely different generator. H027's conditioning and
H031's adjacent rotations do not prove useful relation/root mass.

Construct one N-only adaptive arithmetic relation generator whose dependence
on N escapes that actual fixed-universe counting proof. Changing the label or
permuting the same bounded universe is insufficient. Specify how any new
primes, weights, units or bases are obtained and fully priced. Do not choose
base elements by first factoring hard residuals, quietly grant a useful
smoothness law, or replace generation with the desired oracle. Exact
congruence relations, distinct supply/rank and productive extraction are
separate obligations. Compare against known CFRAC/QS/NFS and Schnorr-type
lattice relation methods before novelty claims.

Seek a structural, costed generation advantage and the narrowest decisive
useful-yield lemma. A finite trial upper bound with no success information
does not meet the objective. If the realization needs a heuristic, write its
actual law, optimize a matched full model and state whether the consequence
would even improve its proper baseline. Do not re-prove H026 or H031.

## Lens C: a recurrence that computes the ECM batch output directly

Exclusive report: research/findings/W002-ecm-norm-recurrence.md.
Exclusive supporting prefix: W002-ecm-*.

Read W001-dynamics Card4, H009's complete finding and ECM-priorart-li2006-note.md.
The full primary Li dissertation and selected page images are now archived.
Cyclic reduction and ordinary quotient-ring division-polynomial recurrence are
already prior art; their multiplicative curve-count/scalar-length work is not
a new escape. H009's finite density screen is not a universal lower bound.

For E_a:y^2=x^3+a*x+1 and P=(0,1), try one explicit recurrence/transformation
computing the batch product of psi_K(P) at supplied parameters, with all
gcd extraction work included, without materializing a degree-r remainder at
each of Theta(log K) stages. A norm-first Ward recurrence is an initial lens:
derive the actual state and all cross terms needed for its updates. Norm
multiplicativity does not make norm(A-B)=norm(A)-norm(B). A growing mixed-moment,
tensor, resultant or polynomial representation must pay for its full size.

Choose one concrete state/transition or a materially justified transformation
within this final-output lens. Do not return the bare norm/resultant notation
as the algorithm. Scalar K and all parameters must be constructed/charged;
K=lcm(1,...,B) has bit length Theta(B). Target a uniform improvement over the
multiplicative r*log K evaluation cost, ideally additive, and state the exact
regime and memory. Independent uniform parameter samples, geometric orbits and
known torsion domains are different distributions. Supply the actual success
and proper-factor extraction consequences or leave them explicitly conditional.
A product gcd=N is not automatically a factor: bound the paid descent, failed
leaves, retries and any extra product queries. A fast single product with
unpriced recovery does not suffice. No special-form cyclic trick or constant
curve-model improvement may be promoted to a new general L constant.

## Handoff

Each report states: exact selected algorithm or failed realization; prior-art
relationship; strongest supported cost and assumptions; verified improvement
NONE unless actually established; decisive limitation and at most one next
preregistered test/proof. Preserve every retrieval limitation and new source
identity. Avoid reading sibling W002 drafts so the lenses remain independent.
The coordinator will synthesize and select independent review, experiments
and focused Lean work only for supported survivors.
