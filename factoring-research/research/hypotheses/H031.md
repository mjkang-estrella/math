# H031 — Coupled-field generation of productive square congruences

2026-10-08. **Constructive analytic round; no accepted algorithmic improvement.**
Verified full factoring complexity improvement: **NONE**.

## Target and prior art

Can an explicit N-only coupling of two number-field relation searches produce
useful modular roots with a proved success law and no more than polynomial
overhead relative to the underlying L_N[1/3] pipeline? Initially require
N=pq with distinct p,q congruent to 3 modulo 4, without supplying their factors.
A result for this family is not an all-input theorem or polynomial-time result.

Lee–Venkatesan section 7 and Remark 7.85 already formulate a productive-root
character and a many-field extension. H028 already reconstructs common rational
columns with separate algebraic ideal blocks. Establish the exact prior-art
relationship first; do not label cross-field parity cancellation or the
Jacobi test itself as a new mechanism.

The actual target is a fully costed sampling/construction law whose probability
of a proper split, including failures through all processing, is at least
bitlength(N)^(-C) for a fixed C uniformly on the claimed family. Preserve a
rigorously justified L[1/3] cost/constant or prove another explicitly improved
matched full bound. Do not silently turn a heuristic field family into the
rigorous Lee–Venkatesan sampler. Maintaining an existing leading constant with
an unproved character hypothesis is not a new result.

## Selected constructive lens

Start from an explicitly generated pair f_1,f_2 with known common modular
root m, using a specified coupled rotation f_2=f_1+(X-m)g if useful. Specify
the law of f_1,m,g and every parameter from N, actual degrees/coefficient
heights, irreducibility failures and required reduction maps. Independent
draws, transforms, isomorphic copies and differing fields are not interchangeable.
Known rotations and rational smoothness reuse are only ingredients.

Try to form actual packets (x,r) with x a unit mod N, r positive and fully
factored over a common prime base, and verified x²=r mod N. The source field's
algebraic product must have a computed square root, with order denominators
checked. The coordinator intake defines exact rational-parity normalization:
two packets with equal parity and opposite normalized Jacobi signs split N.
Check that identity, including its positive-r restriction, but do not stop at
the algebraic criterion.

Provide a concrete method to obtain the matching packets and the sign
mismatch. If you use intersections of parity-image spaces, give finite
matrix/map algorithms with all lifts and root extractions paid. A basis may
require many algebraic roots, so measure that cost explicitly. No uniform
parity vector, independent root signs, favorable image dimension, nonzero
character or cheap search over all dependencies is granted. Common unit masks
preserve root ratios, and fieldwise ± choices only give global sign changes.

Focus on one selected pair-generation realization. Investigate whether its
coupling actually changes the useful-root law or merely rewrites the existing
conjecture. A lemma equivalent to already having a productive congruence is
not an algorithm. If there is no defensible construction/probability argument,
identify the exact first failure and close only that realization.

## Full ledger and decisive boundary

Charge every attempted field/pair, common and separate bases, full valuations,
good/bad-prime treatment, all intermediate records, discarded rows, joins,
matrix dimensions/nonzeros, reconstruction maps, each algebraic root call,
precision/operand widths, random sampling, storage/access, proper gcd tests
and failed trials. Use the repaired expected-work quantifiers in H028.
Expected useful rows alone do not prove cost, rank, attainable quota or a
proper-split law. An event conditional on a rare unpriced filter is not the
target probability. Restarts require a valid iid or conditional analysis.

A successful result needs an exact N-only sampler and uniform complete bound;
a symbolic reduction with a missing oracle does not pass. No theorem about
generic quadratic characters supplies the generated character law without a
proved connection. Compare cold cost with cold cost and rigorous with rigorous.
Any claim improving an NFS heuristic constant needs its own matched model and
cannot be inferred merely from removal of a rigorous fruitfulness assumption.

## Method, ownership and handoff

Read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, current STATE, H031-intake.md, H027's disposition/prior-art
note and H028's corrected report/disposition. Read primary Lee–Venkatesan
Theorems 2.1/2.3, section 7 including Remark 7.85, and Coppersmith's relevant
matrix/root discussion, with exact source identities. No exhaustive novelty
claim is required. H030 is an unrelated live product-construction task.

Symbolic derivation and primary-source inspection/archiving only; no finite
experiment, sweep, benchmark, implementation, Lean edit, packages, recursive
delegation, outside-project writes, commits, publication or scheduler.
A needed experiment must first be proposed for separate preregistration.
Exclusive child files are research/findings/H031-coupled-field-roots.md and
adjacent H031-roots-* sources/scratch. The parent owns all shared files.
Deliver the exact selected construction and proof/cost if obtained, or its
narrowly justified failure. At most one precise revised proof question may
be selected. All new deductions require independent review before acceptance.
