# Frozen target MRC: one lattice per circuit

Myeongjin Kang; no affiliation. Frozen 2026-10-16 before proof attempts on MRC. Original prose CC BY 4.0.

A positive circuit is a finite directed acyclic arithmetic circuit with positive integer inputs, constant 1, addition and multiplication gates, and two designated outputs required to agree. The target is:

There exists a total computable function f which, for EVERY positive circuit equation C, outputs the complete order table of a nonempty finite lattice L_C such that

  C has a solution in positive integers
  if and only if
  L_C is isomorphic to Con(A) for SOME nonempty finite algebra A of SOME finite finitary signature.

The output is one full abstract lattice, not a partial diagram, a list selected using an oracle, an embedding into an ambient congruence lattice, or a subgroup interval whose sizes have been chosen from an already known solution. There is no bound on input circuit size, unknown solution values, algebra carrier, number/arity of operations, or size/height of L_C. The output algorithm must terminate on unsatisfiable as well as satisfiable circuits. Equivalently, together with standard positive semidecidability, the representation predicate is complete for computably enumerable predicates under computable many-one reductions.

The permitted pinned input is family206 at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. All its theorem truths are stipulated. The target is not a request to reassess those theorems. The source's undecidability, computable template-size ceiling, and bounded-witness replacement are antecedents, not new assertions counted here.

Proposed operation to investigate: replace solution-valued literal symmetric-group templates by a finite, solution-independent lattice description that enforces their simultaneous integer readings without admitting additional congruences. The finite-table bound makes finite syntactic completion a plausible route, but does not perform that completion. Any failure must retain the above full target; weak truth-table completeness or a local gadget lemma cannot substitute for it.
