# Research record and uncredited formal endpoint

This lane adds no accepted result. All conclusions are subject to root review. The current campaign count remains 12/20 beyond 39 prior. The reservation metadata says “Exactly40” in one inherited field; TASK.txt and the explicit assignment require exactly 20, which results.json supplies.

## 334599: complete ordinary refutation under the recovered preprint semantics

Write D(A;B) for the unary supervenience connective, interpreted at a world w by

    for every u,v with S(w,u,v), A(u) iff A(v) implies B(u) iff B(v).

No symmetry, reflexivity, transitivity or factorization of S is assumed. Define

    G(A,B) = D(A; A and B).

Then G(A,B) holds at w exactly when B has equal truth values at every S(w,u,v) pair with A true at both endpoints. Proof: on such a pair the antecedent agreement is automatic and the consequent is just B-agreement. Conversely, on any pair agreeing on A, either A is true at both endpoints and the restricted agreement hypothesis applies, or A is false at both and both A-and-B values are false.

Let C00=A and C, C01=A and not C, C10=not A and C, C11=not A and not C. Then

    D(A,C;B) iff G(C00,B) and G(C01,B) and G(C10,B) and G(C11,B).

Indeed, an S-pair agreeing on A and C lies in exactly one cell. Conversely, any pair inside a cell agrees on both A and C. Thus the right side requires exactly the original forbidden-edge exclusions. This argument is valid for arbitrary ternary frames and arbitrary truth sets, including pairs of different worlds with identical atomic valuations. It does not use a false assumption that S(w,-,-) is a complete relation.

Translate every arity-2 formula recursively: preserve atoms and Boolean operations; replace each dependence connective by the four-cell formula using the translations of all three arguments. Structural induction on formulas, including arbitrary nesting, proves truth equivalence at every pointed model. Therefore every arity-2 formula has an arity-1 equivalent. The strict expressivity step at n=1 is false, so the universal hierarchy conjecture is false. One failed step suffices; no stronger all-arity theorem is being counted.

Lean/Hierarchy.lean formalizes actual recursively generated languages, actual ternary frames and their recursive satisfaction relation, the syntax translation, its semantic correctness, strict expressivity, and the exact negation of the universal conjecture. It is not a bounded truth-table theorem or a surrogate predicate. Nat-indexed atoms represent the customary countable propositional vocabulary. World types are arbitrary small types; the translation is uniform in the type. Model.nonempty is unnecessary and the proof works in the stronger setting allowing empty world types too.

### Qualification objections that remain material

The inspected arXiv preprint has Conjecture 15 and Section 7.2 proposing precisely this hierarchy. Its own Section 6.1 uses Boolean cells to eliminate determinacy arities on ordinary Kripke frames; Proposition 16 follows immediately after those cells. Goranko–Kuusisto, arXiv:1609.07398v2 Proposition 3.3 and proof, likewise gives a Boolean normal form on universal frames. These are actual proof-body reads. They do not directly state this arbitrary-ternary-frame endpoint: applying the ordinary-frame result without a bridge would incorrectly collapse the unary language to the agreement language, contradicting the target's own Proposition 9. However, their same cell decomposition plus the one-line guard identity above gives a complete source-adaptation bridge. Under this campaign's strict significance rules this is a serious routine-adaptation objection, not cleared by a Lean proof or an open label. Root should consider it explicitly before any nomination.

The actual journal body (Notre Dame Journal of Formal Logic 60(2), 2019, 283–309) was not read: Project Euclid returned HTTP 200 containing an Incapsula challenge, retained verbatim with a receipt; there was no retry or bypass. A source correction in that body could independently dispose of the lead. The author's arXiv search catalogue and a subject search for supervenience supplied no exact later resolution in the inspected records, but this is bounded and noisy coverage, not worldwide novelty clearance. No publisher-body equivalence is asserted. A current Omega path hit PhenomenalSupervenience.lean was actually read and concerns factorization of a joint public concept, not this syntax-translation theorem.

The certificate is an uncredited research artifact. No acceptance, significance pass, journal fidelity pass or priority claim is made.

