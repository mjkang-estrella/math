# 365943: exact finite obstruction; formalization remains open

This is a research candidate, not an accepted or Lean-certified solution.
Primary definitions: Bašić–Damnjanović, arXiv:2411.16904, Sections 1–3,
Conjecture 16. The 2025 published version retains the conjecture as Conjecture 1.
The current supplementary repository at a135cda6d294bef865045675ec60e0c992c87b48
was read (`sources/nuts-resolver.py`). It uses arbitrary row signs and ILP,
not the symmetric character and shared semi-edge constraint below.

Let a cubic nut graph have a cyclic automorphism σ with eight orbits of size m.
Its one-dimensional real nullspace is σ-stable. After normalizing a nonzero vector
u, σu = εu for ε in {1,-1}. If ε = -1, m is even. In either case, values of u
on each orbit are a nonzero scalar times the character j ↦ ε^j.
The corresponding Fourier quotient matrix C is real symmetric and has a full
nullvector. Its kernel must have dimension exactly one, since every kernel vector
lifts injectively to a graph nullvector. The ordinary unsigned quotient is A.

Each quotient row has total absolute weight three. Ordinary edges contribute ±1;
a double edge must have equal character signs on its two contributions. Otherwise
the contributions cancel, forcing the third neighbor's nonzero nullvector value
to vanish. Loops contribute ±2. A semi-edge comes from shift m/2 and contributes
ε^(m/2), the SAME sign at every semi-edge. Thus |C| = A, and all diagonal entries
of absolute value one have equal sign. All A have nonnegative integer entries,
are symmetric, have row sum three, and connected subcubic underlying graph.
A diagonal two is a loop; a diagonal one is a semi-edge. Connectedness rules out
triple edges and isolated quotient vertices. Switching C by a diagonal ±1 matrix
makes every edge of a chosen underlying spanning tree positive, preserving
nullity, fullness, and diagonal signs.

An independent canonical augmentation generates all connected subcubic graphs
through order eight: 1, 1, 2, 6, 10, 29, 64, 194 for orders one through eight.
Completeness argument: a connected graph has a vertex whose deletion is connected
(take a leaf of any spanning tree); remove it and apply induction. Add it back
with its one, two, or three neighbors. Canonicalization examines every choice in
an individualized cell, refining by neighbor counts, so isomorphic inputs share
an output and every output is a relabeling. Exact set equality with the McKay
catalogue is checked, not just count equality. This is an ordinary algorithmic
argument; no Lean theorem for that completeness statement is supplied.

For the 194 graphs, `nuts_exact.py` augments each edge with zero or one duplicate
and fills each remaining row deficit with a diagonal entry. This gives 669
representations, with harmless isomorphic duplicates. The source has 534 after
isomorphism reduction; we do not claim our 669 are distinct. If A has a kernel of
dimension at least two, or a nonfull kernel vector, its trivial-character lift
already prevents any nut graph. The final run uses exact rational nullspaces for
this pretest. Then all symmetric signings modulo spanning-tree switching are
examined. The shared semi-edge sign restriction leaves 7,176 matrices after
that pretest. Each has either a nonzero determinant (7,030) or a zero diagonal
cofactor (146), independently checked by integer Bareiss elimination.

For a real symmetric matrix of rank seven, its adjugate is a nonzero scalar
multiple of vvᵀ for a kernel generator v. A zero diagonal cofactor therefore
forces v to have a zero coordinate. Rank at most six prevents one-dimensional
kernel. Thus all of these exact certificates exclude a full one-dimensional
kernel, completing an ordinary computer-assisted obstruction conditional on the
stated enumeration and quotient reduction. The earlier floating-point run is
only diagnostic. Its 132 full-nullity signings all have both semi-edge signs;
none satisfies the character constraint. The randomized lift scripts tried ZERO
actual voltage assignments: all were rejected by the parity preconditions. They
are not experimental search coverage and do not support a nonexistence claim.

## Precise remaining formal obligations

1. Formalize a finite graph with a free cyclic action with eight equal orbits;
   prove its real one-dimensional full kernel transforms by ε = ±1.
2. Prove the symmetric signed quotient, no cancellation at double edges,
   shared semi-edge sign, and injective kernel lift statements.
3. Prove spanning-tree switching and completeness of the independent connected
   subcubic graph generator and the augmentation/signing generator.
4. Kernel-check all generated determinant/cofactor certificates and prove the
   adjugate support lemma, including rank-deficient cases.
5. Compose those into the literal universal nonexistence theorem. Then strict
   extracted replay, all-declaration axiom audit, independent review, and root
   significance/novelty assessment are required.

No surrogate endpoint, added axiom, or bounded Lean theorem is offered as the
conjecture. No acceptance credit is claimed. This finite reduction appears useful,
but its novelty and significance have not been independently adjudicated.
