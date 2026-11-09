# W003 — Constructing relations without revealing the sampled root

2026-10-08. **Symbolic constructive wave; no accepted new result.**
Verified COMPLETE classical factoring complexity improvement: **NONE**.

W002 is complete. Its three corrected dispositions accept narrow algebra and
cost statements but close all three realizations as speedups. In particular,
many square dependencies can have entirely trivial productive image. This
wave investigates an explicit change to the generation interface, not a new
name for the unproved character-independence condition.

## Objective and inherited boundary

Find a uniform classical N-only algorithm with lower complete factoring cost.
Keep rigorous complete-factorization bounds, conditional/heuristic NFS costs,
deterministic power bounds and special families distinct. A target here is
to retain subexponential relation costs while establishing useful-root
probability for the actual generation law. A rigorous L_N[1/3,O(1)] complete
algorithm would be a different achievement from improving heuristic GNFS's
constant. Neither is predicted or assumed.

Read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, current STATE and W001 synthesis. Also read the W002 B/C
dispositions, H027's corrected section on root fibers and its disposition,
H027-root-entropy-prior-art.md, H028/H031 dispositions, and relevant original
reports for any dependency actually used. Do not rely on old provisional
labels or stale historical lifecycle text over the current dispositions.

H027 already states a sufficient root-fiber condition. Lee–Venkatesan already
identify the productive-character gap, including multiple polynomials. Rabin's
root-inversion reduction and Dixon's uniform-square method are prior art.
Restating those reductions, granting a square-root oracle, or assuming an
odd target is attainable does not satisfy this brief. Current primary leads:

- https://arxiv.org/html/1805.08873v1 (Theorems 2.1/2.3 and section 7).
- https://dspace.mit.edu/entities/publication/15016449-ca26-4d45-82ea-7c200d82d777
  (Rabin, MIT-LCS-TR-212; coordinator checked repository metadata only).
- H027-adaptive-source-dixon-1981.pdf and its source ledger.
- H028/H031's archived Coppersmith and field-square-root sources.

Each child has exclusive outputs, no sibling-draft reads and no recursive
delegation. Parent owns shared state, code and acceptance. This wave allows
symbolic derivation and primary-source inspection/archiving only: no numerical
experiment, example search, benchmark, solver implementation, Lean action,
package install, outside-project write, commit, publication or scheduler.
If a finite test becomes essential, propose one separately with frozen inputs,
seeds, full budgets and a rejection criterion before later authorization.

## Concrete interface to investigate, not a supplied oracle

After paid elementary cases, sample an n-bit word x. Charge rejects x>=N;
inspect gcd(x,N), returning a verified proper factor when possible and counting
full-gcd failures. On a unit branch form R=x^2 mod N. A proposed inner
construction receives only N, R and fresh independent randomness, never x
or any data depending on x beyond R. Selection, stopping and all failures must
respect this restriction. The outer routine may retain x for final recovery.

The known root-inversion reduction suggests an exact conditional useful-root
law if this inner construction outputs a verified y with y^2=R modulo N.
Check its domains, finite-tape law, factor multiplicities and rejected words.
This law alone is not the proposed advance. The hard task is constructing y
with paid generation, reconstruction and a proved adequate probability of
completion. A successful inner law may depend on R but cannot silently
condition on which preimage x was sampled. No known-factor input is allowed.

One possible relation interface is v_j=R^epsilon_j m_j^2 modulo N with
epsilon_j in {0,1}, signed integer v_j and verified unit m_j, all constructed
without x. An integer-square product with odd total epsilon would give a
root of R after paid reconstruction. A zero/nonunit multiplier needs its own
factor-or-failure handling. An even dependency does not supply the desired
odd target merely because the ordinary square kernel is large. Price the
algorithm finding that target; a full square-class oracle is not available.

## Lens A — mixed square-class targets in two number fields

Exclusive report: research/findings/W003-twisted-fields.md.
Exclusive supporting prefix: W003-twisted-*.

Investigate this specific attempted realization. Construct two irreducible
integer polynomials f_1,f_2 from N,R with f_i(R)=0 modulo N, and fields
K_i=Q(alpha_i). The selection rule, coefficient heights, degrees and all
rejections must be explicit and paid. Do not import a small common root or
NFS polynomial-selection law that the actual R distribution does not have.

For common integer pairs (a_j,b_j), the elements a_j^2-b_j^2 alpha_i map
to the same residue a_j^2-b_j^2 R. For a selected subset let
Q(T)=product_j(a_j^2-b_j^2 T). The proposed mixed target is

    Q(alpha_1)=alpha_1 * z_1^2,    Q(alpha_2)=z_2^2,

with actual field roots and valid reductions of z_i. If their reduced images
are units, their ratio is a candidate root of R. This sketch does not assert
that such a subset exists, is cheaply found, or has low norms. Derive the
recovery carefully, with denominator-cleared maps, zero/nonunit images,
reducible polynomials, field embeddings and the opposite target orientation.

Develop one finite algorithm that tries this mixed target. Explain what
information lets its matrix or other search find an inhomogeneous square-class
condition, including units and ideal-class obstructions. Actual root tests
are paid; parity of ideal exponents alone is insufficient. If a square-class
basis or exhaustive subset search is necessary, expose that cost rather than
granting it. Determine whether sign-paired generation forces the target to
be trivial or unattainable, and whether using arbitrary roots R destroys the
usual small-norm geometry. Charge the complete cold trial and restart law.

Compare with existing two-field NFS and modular-square-root methods before
any novelty claim. Seek an actual cost/success improvement; if this specific
realization fails, identify its first concrete obstruction without claiming
all such root-independent constructions impossible. No larger H031 rotation
scan or repetition of its conditional character model is requested.

## Lens B — independent primary-source and reduction gate

Exclusive report: research/findings/W003-root-inversion-priorart.md.
Exclusive supporting prefix: W003-root-priorart-*.

Independently check the exact reduction and closest primary prior art for
modular root inversion by relation methods, target square classes, two-field
NFS, quadratic extensions/involutions and rational norm compression. Do not
read Lens A's draft. Determine which parts of the mixed-target sketch are
already existing algorithms and what their complete costs and success
premises actually prove. Inspect primary theorem statements and relevant
algorithms, not only abstracts or search snippets; record retrieval failures.

In particular, distinguish a supplied square-root oracle from a construction,
homogeneous square-kernel availability from an inhomogeneous target, and a
root-fiber reduction from proof that a modified NFS generator retains the
original relation-supply theorem. An exact distributional coupling needs
proof. Check whether known algorithms already realize this interface, even
at a worse bound; do not manufacture novelty from different terminology.

Give a concise algorithm/cost map and a decisive consequence for Lens A's
research question. Any new deductions remain unaccepted pending review.
Do not turn a missing theorem in the bounded search into a lower bound or
a claim that no relevant literature exists.

## Delivery and acceptance

State the finite algorithm or exact source-supported limitation; complete
time/space/probability accounting; matched comparison; unsupported statement;
and at most one concrete next proof/test that could change the conclusion.
Distinguish conjectures, on-paper constructions, observed evidence and accepted
results. Preserve frozen brief/input identities and a separate delivery
manifest. New major deductions require a separate independent review round.
No infrastructure or theorem-count task is selected as a substitute for the
user's asymptotic objective.
