Staircase integral regular summand: scoped Lean support
Myeongjin Kang, no affiliation. 2026-10-15. Original code/documentation: MIT.

STATUS
Fresh supporting-source compilation and kernel-checked controls PASS with Lean
4.34.1 (compiler commit 5045d0056413266e57c625dcd7c365b10e377c52) and
mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. Independent semantic audit
is pending. This package supplies neither a full staircase formalization nor
acceptance/count credit. The existing partial source was reused and completed.

EXACT MATHEMATICAL INTERFACE
Let R be any commutative unital ring, G any finite group, M any R-module,
rho : G -> End_R(M) a representation, z in M, and theta : M ->_R R linear.
The sole representation-specific hypothesis of the splitting results is

  Separates rho z theta : forall g, theta(rho(g) z) = if g = 1 then 1 else 0.

Neither existence of z/theta nor this condition for a Specht cube is asserted.
This is a general conditional theorem, applicable to many representations.
No nontriviality, characteristic, field, freeness of M or division assumption
is used. The zero ring is permitted.

The regular module is represented in finite function coordinates G -> R,
with action (h.a)(g) = a(h^-1 g). Since G is finite these are regular free
coordinates, mathematically equivalent to the usual finitely supported group
algebra basis. An explicit equivalence to MonoidAlgebra is not constructed.
The definitions and proved conclusions are:

  I(a) = sum_g a(g) rho(g) z             [orbitMap]
  P(x)(g) = theta(rho(g^-1) x)           [coefficientMap]
  I(h.a) = rho(h) I(a)                  [orbitMap_equivariant]
  P(rho(h) x) = h.P(x)                  [coefficientMap_equivariant]
  P(rho(h) z) = delta_h                 [coefficientMap_orbit, using Separates]
  P.comp I = id                        [coefficientMap_comp_orbitMap]
  I is injective                       [orbitMap_injective]
  x - I(P(x)) belongs to ker P          [complement_mem_ker]
  IsCompl (range I) (ker P)             [range_isCompl_ker]
  range I and ker P are G-stable        [range_stable, ker_stable].

The last three results give an actual invariant complementary submodule.
An explicit LinearEquiv to a product of submodule types is not packaged.
The action and equivariance are expressed using Representation and R-linear
maps, rather than maps bundled as R[G]-linear morphisms.

For any commutative R-algebra A and any R-linear maps i : V -> W, p : W -> V,
baseChange_split proves that p.comp i = id implies
  (p.baseChange A).comp (i.baseChange A) = id.
baseChange_injective deduces injectivity. baseChange_intertwines proves
preservation of an intertwining equation f.comp u = v.comp f. These use
mathlib's A-linear tensor maps on A tensor_R V and A tensor_R W, without
flatness. They can be applied to the preceding orbit/retraction maps. We do
not construct the scalar-extended representation as a separately bundled
Representation, or identify base-changed Specht lattices/tensor cubes.

integer_deficits_vanish proves that for any finite index set s and integer
functions d,r, sum_(i in s) (d(i)-r(i))^2 = 0 implies d(i)=r(i) for every i
in s. This is the zero-deficit implication for individual integer support
terms. The palette hypotheses, row moment identities, and global square
budget needed to establish its premise are NOT proved here.

COVERAGE AGAINST THE PAPER
paper-correspondence.json records the precise links to the frozen candidate
and the read-only manuscript snapshot (including that snapshot's hash).
In staircase-manuscript/main.tex, eq:coordinate corresponds to coefficientMap
as a formula, without proving its equality to J_m^-1 pi_D q^B. eq:product is
the UNPROVED staircase instance of Separates. The downstream splitting and
base-change steps in the proof of thm:main are covered abstractly conditional
on that instance. In prop:unit, only the zero-sum-of-integer-squares implication
after eq:deficit is covered. Neither prop:unit nor thm:main is formalized.

Omitted in particular: the triangular diagram and its cardinality, Specht
lattices/polytabloids, the tensor-cube generator, ambient embeddings, q^B,
content projection, J_m, palette uniqueness (lem:palette), expansion support,
the positive unit sign, the construction/existence of a staircase separating
functional, all-m staircase instantiation, Specht base-change identifications,
and constituent or projective multiplicity consequences. There is no axiom
or disguised hypothesis asserting the full target.

ATTRIBUTION AND DEPENDENCIES
The coordinate-functional regular-summand mechanism is classical, credited
to Bryant--Kovacs (1972), Lemma (ii)--(iii), as explained by the contribution
review. It is not claimed as a new theorem. The staircase triangular uniqueness
is credited to Ikenmeyer (2015) and is not formalized here. The square-deficit
mechanism is inherited from the pinned cyclic-polytabloid source; this file
only proves its elementary integer vanishing step. Full proof and narrowly
SUBSTANTIAL contribution reviews are input context, not Lean premises.
No OpenAI upstream mathematical theorem is invoked by this Lean source.

VALIDATION AND CONTROLS
Checks.lean prints exact types (with implicit parameters and universes) and
axiom closures for all 20 public declarations: 16 theorems and 4 definitions.
logs/types-and-axioms.log contains the full compiler output. Controls.lean
has six kernel-checked results: a separating functional in the integral
regular representation of C3, its positive split identity, and four negative
controls. Those prove that dropping g^-1 in P, negating z, using positive
coordinate shifts for the specified left action, and reversing a left-inverse
identity fail in concrete examples. The direction control uses inclusion
Z -> Z x Z and first-coordinate projection; the reverse composite is not id.
Finite decidable arithmetic in C3 is proved with kernel-reduced `decide`;
there is no native_decide, external oracle, or finite check substituted for a
general theorem. These controls test the abstract maps, not staircase signs.

All accepted compilations have exit code zero, no warnings, and axiom sets
contained in propext, Classical.choice, Quot.sound. No sorry, admit, unsafe,
custom axiom, or native_decide declaration is present. Empty logs/source.log
is the complete, silent successful source compilation, not a missing log.

REPRODUCTION
From this directory:
  python3 -B rebuild.py
  python3 -B verify.py

rebuild.py accepts --lean /path/to/lean and --cache /path/to/.lake/packages.
Defaults use the exact paths from the brief. It checks each package revision
against lake-manifest.json, checks the compiler commit, then copies the three
Lean files to a fresh temporary directory INSIDE this assigned directory.
It compiles StaircaseSupport.olean from source and then imports that fresh
artifact for the type/axiom checks and controls. Temporary output is deleted.
No supplied/previous StaircaseSupport.olean is trusted. Shared dependency
caches are read only, not rebuilt, and no network is used. Their precompiled
mathlib/dependency artifacts remain part of the trusted setup; this is not a
fresh dependency build or an audit of upstream library correctness.

Actual full compiler logs, compiler version, commands/exit codes, source and
fresh olean digests, dependency revisions, and scope flags are recorded in
logs/ and validation.json. input-manifest.json records full input hashes and
honest read extents. output-manifest.json covers every delivered file except
itself; verify.py checks its inventory and hashes plus source/log receipt
consistency and the frozen input hashes without modifying any file. A changed
input or generated receipt requires an explicit new manifest by the integrator.
No shared indexes, manuscript files, caches or dependencies were edited. No
staging, commits, uploads, or additional agents were used. The parent should
arrange the independent semantic Lean review before package inclusion.
