SCOPED LEAN SUPPORT FOR THE KINETIC PATH THEOREM

Author: Myeongjin Kang. No affiliation. Original code and accompanying code
documentation are MIT licensed. The full analytic theorem is not formalized.

Nine general supporting declarations cover elastic collision momentum and
squared-norm energy in any real inner product space; the affine common-time
shift and relative-origin shear used in the extended history coordinates;
finite all-line energy under a pair replacement and under the concrete elastic
pair update; and exact rational exponents in the transfer/chaining budget.
The normal is explicitly unit through inner n n = 1; the two updated labels
are explicitly distinct; all other velocities stay fixed. Both new velocities
are computed from the old pair. No geometric, measure or probability axiom is
introduced. These are supporting identities, not new research results.

In particular contact_time_shift assumes the same time shift on the two
contact trajectories. It does not prove that the entering-root construction
has that covariance, that chronology Q is invariant, or that a coordinate
change preserves measure. total_collision_energy proves one finite population
update, not the existence or almost-sure validity of an entire physical flow.
The window bound, decorated kernel estimate, Gaussian reserves, microscopic
union bounds, C-tightness and J1 limit remain prose mathematics.

Reproduce with the pinned Lean binary directory on PATH:
  lake build
  python verify.py

The checked-in Lake manifest pins mathlib and dependencies. This session reused
the existing campaign/formal package cache via an ignored local symlink; a
fresh network installation was not tested. verify.py compiles a copied source
to a fresh temporary olean, then checks all nine exact types and their axiom
lists against that olean. Only propext, Classical.choice and Quot.sound are
allowed. Build artifacts and cached oleans are not distributed as evidence.

Initial implementation failures were local tool-path lookup and Lean API/
document-comment placement errors. These were corrected without narrowing
the mathematical statements. Final logs record actual fresh compilation.
Independent semantic review is separately recorded when completed.
