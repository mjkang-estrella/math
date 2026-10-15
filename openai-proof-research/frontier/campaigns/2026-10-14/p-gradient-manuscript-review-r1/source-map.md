# Source interfaces and reading boundary

This is a manuscript gate, not a new proof of the cited classical theorems
or an audit of stipulated upstream truth. The complete prior reviews and
all four mathematical inputs were read. Their verdicts were not substituted
for checking the new manuscript deductions. The implementer's full
consolidation report, claim map, input/output manifests and exact appendix
delta were also read and checked against the actual files.

## Stipulated pinned primary statements

Repository: `https://github.com/openai/math`; immutable revision
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, as in
`sources/upstream.json`. The local cache prefix is

    frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/
    Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/
    build/manuscript/sections/

Each primary file has the corresponding pinned raw URL

    https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/FILE

The local bytes were read and their hashes checked against the existing
authenticated values; this review did not re-fetch the pinned files.

| File and theorem labels | Exact interface used | Reading in this review |
|---|---|---|
| `01-introduction.tex`, `thm:main` | All bounded continuous infinity-harmonic functions, d >= 3; dimension-only C1,alpha estimate with alpha in (0,1/3]. | Introduction and theorem statement through its scaling consequence. |
| `02-flatness.tex`, `lem:linear-lift` | Infinity-harmonic u on an arbitrary original dimension lifts as u(y)+b; no nonzero original gradient assumption. | Complete statement and proof. |
| `02-flatness.tex`, `lem:sum-rule` | Continuous summands, local interior maximum, C2 test; closed upper jets with block Hessian <= A+eta A^2. | Actual statement and preceding jet convention. This general theorem of sums has no PDE-specific or dimension-three restriction. |
| `03-reduction.tex`, `thm:liouville` | Continuous entire solution of X[(q_x,1)]=0, m >= 1, finite C0, all-center/all-radius FIT; affinity. | Actual statement, geometric selection/comparison/extraction and derivative extraction. The source PDE passage for rescaled infinity solutions is not imported for finite p. |
| `03-reduction.tex`, `lem:cylinder-comparison` | Same parameter theta^2, common positive lower/finite upper slope norms; comparable concentric radii or equal-radius quarter margins; quadratic norm and first-order direction differences. | Actual statement and geometric proof, with attention to the equal-parameter limitation. |
| `04-limiting-tools.tex`, `lem:frame-invariance`, `lem:fit-compactness` | Fit transformation, parameter bounds, local compactness, logarithmic growth and subquadratic tails. | Statements and the fit-only comparison/compactness argument. Its original PDE clause is replaced by G_tau stability after verifying the changed frame formula. Other PDE envelope properties in this source are not used. |
| `05-envelope-contact.tex`, `lem:barycentric-envelope` | For continuous functions with subquadratic spatial growth: measure/finite configuration equality, finite attainment, continuity, duality and concave-envelope identity. | Statement and geometric duality/attainment argument. The common-time sum-rule construction was read as an interface; the added tau-trace calculation was checked in the manuscript itself. |

All applications satisfy the stated dimension hypotheses, notably the
initial n-to-n+1 infinity lift and the finite-viscosity projection to
m=n-1 >= 1. I did not audit the proofs inside the stipulated infinity
regularity/Liouville result or read its remaining Sections 6–8.

## Classical primary interfaces

**Uhlenbeck.** Primary scan:
[Regularity for a class of non-linear elliptic systems](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6219-11511_2006_Article_BF02392316.pdf),
Acta Math. 138 (1977), 219–240. Used the existing PDF and extracted text
in `p-gradient-uniformity/sources/`. Read Sections 1–6 in the extracted
text, including the actual structural theorem and scalar specialization,
Moser statements (2.1)–(2.3), weighted differentiability/supremum estimates,
linear comparison and perturbation iteration, (5.1), (5.4)–(5.5), and (6.1).
Some extracted formulas are OCR-garbled. Printed pages 234 and 238 were
therefore inspected from the existing images for the reference update
and the two decisive decrease inequalities. I did not independently
reprove Moser theory, the general elliptic-complex results, or the general
weak difference-quotient justification. The scalar parameter-uniform
deductions and every smallness choice used here were checked separately.

**Savin.** Primary author copy:
[Small perturbation solutions for elliptic equations](https://www.math.columbia.edu/~savin/Small_pert.pdf),
CPDE 32 (2007), 557–578. Used `/tmp/frontier-typeset/savin.pdf` and its
text. Read H1–H4 and Theorems 1.1/1.3, Corollary 3.3, and Proposition
4.1 with its varying-F_k proof (printed pp. 571–573). Inspected rendered
pp. 558,560,572 to resolve the ellipticity norm, absolute small-solution
bound and varying-operator statement. The proof of earlier Harnack
theory on pp. 561–568 and Section 5 applications were not re-audited.
No claim of new Savin theory is made. Restricting the common jet radius,
if necessary, ensures the entire positive-increment segment in H2 stays
within the assumed derivative neighborhood. The actual applied F_d is
linear in X, so its matrix ellipticity depends only on q.

**Kotschwar–Ni.**
[arXiv:0711.2291v1](https://arxiv.org/abs/0711.2291v1), Theorem 1.1,
is retained as the same classical positive-p-harmonic gradient input
whose exact statement and constants appear in the round-1 review.
I checked the manuscript's substitutions and uniform algebra against
that recorded statement; I did not perform a new reading of this
primary proof. This is not an expanded reading claim.

**Julin–Juutinen.** Read the primary
[arXiv:1104.2197v1 HTML](https://arxiv.org/html/1104.2197v1), introduction,
Section 2, Theorem 3.1 and Remark 3.3. It identifies continuous weak and
viscosity solutions and explicitly permits ordinary tests when p >= 2.
Remark 3.3 supplies a.e. Hessian convergence of mollifications of a
semiconcave function. The manuscript's flux argument uses the semiconvex
sign-reversed version. I checked the polynomial operator identification
at zero and nonzero gradients and the new flux/Fatou passage; I did not
reprove all nonlinear potential theory cited in that primary paper.

**Linear Harnack.** Read Sections 2–3 and the stated Sobolev restriction
of the primary
[Crescimbeni–Forzani–Perini article](https://ejde.math.txstate.edu/Volumes/2007/38/crescimbeni.pdf),
EJDE 2007 no. 38: measurable symmetric coefficients with positive finite
ellipticity, weak W1,2 solutions, Theorems 3.1–3.2. These give the
solution Harnack/continuity interface used in contact propagation.
The paper's Sobolev exponent is written for total dimension above two;
the manuscript's explicit diag(B,1) extension handles total dimension
two. I verified that new extension by Fubini. The Harnack proof itself
and Lax–Milgram/trace theory remain classical citations.

**Other classical facts.** Arzela–Ascoli, standard viscosity stability,
Alexandrov's theorem, Sobolev/Poincare, constant-coefficient linear
interior estimates, Lax–Milgram and Sobolev traces are used in their
stated classical forms. The Sanchez-Morgado citation is not load-bearing:
the exponential flux derivative used here is calculated explicitly.

## Section 1 comparison and corollary interfaces

These readings check only the manuscript's stated comparisons and
corollary, not literature priority or exhaustiveness.

* [Peng–Zhang–Zhou, arXiv:2310.08093v4](https://arxiv.org/pdf/2310.08093v4):
  read the convex-ring setup and Theorem 1.1 in the primary PDF. The
  statement gives C1 convergence of the potentials and nonvanishing
  limiting gradient in that setting. The HTML opened initially but
  failed when revisited, so the PDF was downloaded into this review's
  `checks/` directory and its actual theorem block read.
* [Bungert, arXiv:2302.08462v2](https://arxiv.org/html/2302.08462v2):
  read Theorem 1. It is a value-convergence estimate with a common
  value-Holder bound and boundary error; a positive gradient lower
  bound improves its rate. It supplies no unrestricted common gradient
  Holder bound of the claimed kind.
* [Sobral–Teixeira–Urbano, arXiv:2610.13137v1](https://arxiv.org/html/2610.13137v1):
  read Theorem 1.1 and Lemma 2.2. The constants depend on p; the
  large-shift linear matrix is I+(p-2)e tensor e, with ellipticity
  ratio p-1. The manuscript's comparison and joint-limit observation
  have the correct scope.
* [Lee–Lee, arXiv:2609.09966v1](https://arxiv.org/html/2609.09966v1):
  read Theorems 1.2/1.3 and the actual Theorem A. The latter requires
  a quantitative homogeneous exponent alpha_0 > 1/(p-1), below 1,
  and gives the inhomogeneous endpoint with p-dependent constants.
  The manuscript supplies this antecedent for fixed
  p > max(3,1+1/alpha_n): its gradient bound plus the trivial value
  bound gives the full homogeneous C1,alpha norm required there.
  I did not independently open the earlier 2018 transfer paper that
  Lee–Lee quote. The manuscript cites Lee–Lee's actual Theorem A.

The full inhomogeneous conjecture and worldwide priority are outside
this review. No MathDB status assertion is needed for the proof verdict.

## Internal proof dependency and formal boundary

The four-text union consists of the unchanged I345 analysis, repair
addendum, compact-p lemma and frozen appendix at the prescribed SHA-256s.
Their complete sources, not just their gate labels, were compared with
the active manuscript. The frozen appendix's paid operations were
reconstructed directly from its proof. This review did not reread the
entire earlier I236/I239 archive separately; the complete r2 audit and
its operation trace were read. The actual expanded typeset appendix
is fully covered through the frozen text and exact reviewed delta.

Both Lean modules were read completely and elaborated from source
copies containing only appended #print axioms commands, using Lean
4.34.1 and existing mathlib oleans at
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The actual vector physical
form, sqrt substitution, hypotheses and both constants match the paper.
Only zero-jet algebra is formalized; no analytic or novelty statement
is thereby certified. See the runnable checks and axiom outputs.
