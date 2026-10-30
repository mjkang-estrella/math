# Bergman–Rubin Conjecture 2: unresolved research report

No full proof, counterexample, or discovery nomination. Credit 0. No Lean endpoint.
All reductions below are auxiliary and uncredited.

## Literal target and known scope

Source: arXiv:2309.02047v2, printed p27, Conjecture 2. For c≠0,
m∈N positive, rational s_k≥1 with ms_k integral, and |a_k|≥1,
P=c∏(z−a_k)^(ms_k), f any analytic branch P^(1/m) in the disc,
S=Σs_k. Prove ||f'||_T≤(S/2)||f||_T, with equality exactly when
all roots are unimodular. Boundary values of derivative moduli are understood
by continuous extension. Moduli are branch independent. Empty/constant and
zero-c degeneracies are not targets.

Read the actual source Theorem 4 and its proof (pp9–13), Theorem 5 and
its reflection proof (pp13–15), and Conjecture 2. Theorem 4 already proves
all-boundary equality for real weights≥1. Theorem 5 allows arbitrary such
boundary weights but requires integer weights for exterior roots. It factors
f+ζf* into the boundary-power factor times a polynomial with boundary zeros;
this is exactly the step unavailable for fractional exterior weights.
Neither theorem gives the full conjecture.

The root notes were read from current filesystem bytes and frozen by hash
in provenance.json. No git operation was used, so their identification with
the user-specified historical commit 3a32fdd737 was not independently checked.
The exact source PDF/text and the root source render are hashed as local inputs.

## Rechecked existing reductions

For λ=min s_k≥1, write g=∏(z−a_k)^(s_k/λ), adjusting constant moduli
if necessary. Then |f'|=λ|g|^(λ−1)|g'|, so the full min-weight-one
inequality and its strict exterior case imply the entire target. If g's
inequality is strict, the second step in

    ||f'|| ≤ λ ||g||^(λ−1) ||g'|| ≤ (S/2)||g||^λ

is strict. Boundary equality is already known. Common powers of ordinary
polynomials are classical consequences, not outcomes.

For L(z)=Σs_k/(z−a_k), f'=fL. With a common denominator m,

    (f')^m = C ∏(z−a_k)^(m(s_k−1)) H(z)^m,
    H(z)=Σ_k s_k ∏_{j≠k}(z−a_j).

This is an ordinary polynomial of degree m(S−1), since H has leading
coefficient S. Bernstein at a nonzero derivative maximizer gives the known
local second-derivative restriction, not the desired comparison of norms.

The root's quadratic obstruction checks exactly: a=1+i/10,b=−3−i/10,
f'=2z+2 has unique maximum 4 at 1, but
|f'(1)/f(1)|²=160000/1601>1. Nevertheless
|f(−1)|²=160801/10000>16. This refutes the local shortcut only.
No new random numerical search was performed.

## New exact obstruction to a radial variational shortcut

It would suffice to prove that moving each exterior root inward to its radial
projection never decreases R=||f'||/||f||. That monotonicity is false, even
for ordinary quadratics (and therefore cannot be assumed in the larger class).

Let p_r(z)=(z−r)(z+3), r≥1. For |z|=1 put x=Re z. Directly,

    |p_r(z)|²=(1+r²−2rx)(10+6x)=A+Bx−Cx²,
    A=10(1+r²), B=2[3(1+r²)−10r], C=12r.

At r=3 the vertex is x=0, ||p_3||²=100, ||p_3'||=2, R_3²=1/25.
At r=4 the vertex is x=11/48∈(−1,1),
||p_4||²=8281/48, ||p_4'||=3, R_4²=432/8281>1/25.
The derivative norms are exact by the triangle inequality for 2z+(3−r),
with equality attained on the circle. Both roots remain strictly exterior.
Both examples satisfy the actual Erdos–Lax inequality strictly; this is NOT
its counterexample. It disproves monotonicity of the normalized ratio too,
since S=2 is fixed. A nonmonotone global deformation is not excluded.
The rational arithmetic is executable in checks/exact_routes.py.

## A limited variational reduction and its precise obstruction

Here is an ordinary lemma, not a full global mechanism. Fix weights s_k≥1,
and vary root positions, allowing each strictly exterior root to vary freely
in a small complex neighbourhood. Assume a configuration is a local maximum
of R. Suppose |f| has a unique maximizing point w∈T, and choose a derivative
maximizer z∈T for which f(z)≠0 and f'(z)≠0. Then there cannot be two
distinct strictly exterior root positions.

Proof. Keep this z fixed. The quantity

    F(a)=log|f'_a(z)| − log||f_a||

is at most log R(a), with equality at the base configuration. Thus it too
has a local maximum there. The unique maximizing point w makes the norm
term differentiable under exterior-root perturbations: compactness puts
nearby maximizers near w, and the usual upper/lower difference-quotient
sandwich gives the derivative of log|f_a(w)|. All these points avoid zeros.
Equivalently apply the argument to |f_a|², whose parameter derivative is
uniformly continuous on the circle for exterior-root perturbations.

For a free root a of weight s, differentiate in arbitrary complex direction
δa. The differential of F is

    s Re{[−1/(z−a) + 1/((z−a)²L(z)) + 1/(w−a)] δa}.

It must vanish for all δa. Consequently each free exterior root satisfies

    (z−w)(z−a)L(z)+(w−a)=0.                         (*)

The left side is linear in a, with constant coefficient
(z−w)zL+w and a-coefficient −[(z−w)L+1]. Two distinct roots a force
both coefficients to vanish. The latter gives (z−w)L=−1, which makes
the former w−z=0, a contradiction. This proves the limited lemma.

This does not prove the conjecture. In particular:

* A supremizing sequence might escape to infinity or collide with boundary
  roots. No compactness or strictness argument has been supplied.
* The function norm may have multiple maximizing points. The denominator's
  directional derivative is then a maximum over active points, not the
  derivative at one common w. Rootwise stationarity uses convex combinations
  of 1/(w−a), so the single linear equation (*) no longer follows.
* Even with a unique w, the lemma leaves configurations with one exterior
  root position (of arbitrary noninteger weight) and arbitrary boundary roots.
  This is not covered by Theorem 5.
* A derivative maximizer at a boundary zero is outside the displayed log
  calculation. No elimination of this possibility is claimed.

The radial obstruction above actually has two conjugate function-norm
maximizers at both r=3 and r=4. Thus multiple active points occur in very
simple admissible examples; a proof may not discard them as exceptional.
The lemma and obstruction are research notes, not independently reviewed
new-to-literature claims or separate credit.

## Equivalent weighted polynomial target

For strictly exterior roots (so no boundary division issue), the desired
inequality is exactly

    max_T |P'| |P|^(1/m−1) ≤ (deg P)/2 · ||P||^(1/m).

This is a weighted norm of the ordinary derivative with the negative power
weight |P|^(1/m−1), together with the multiplicity constraint at every root.
Ordinary Lax only gives ||P'||≤(deg P)/2||P|| and does not allow this weight
to be inserted. At boundary roots the displayed weighted quantity is defined
by its continuous combined expression, not by separately evaluating 0 to a
negative power. This reformulation isolates the missing weighted estimate;
it is not a proof.

## Actual classical body comparisons

Erdélyi, Canadian J. Math.43(3) (1991), pp495–505, DOI
10.4153/CJM-1991-030-3: retrieved the actual author-hosted BMIGNP.pdf.
The author list's pages1–11 are inconsistent with the actual article pagination;
use the PDF's495–505. Definitions2.6–2.13 introduce generalized complex
products, but the paper explicitly restricts the studied functions to the real
line and studies their moduli. Theorem3.1 bounds the real derivative of a
nonnegative trigonometric modulus by c_1 N times its supremum, with c_1
an unspecified absolute constant. Theorems3.2/3.3 are real-interval bounds.
They do not supply sharp S/2 or control the missing phase derivative.

Erdélyi, JAT68 (1992), pp283–305, author-hosted WMB.pdf: read definitions
and main Theorems1–3. Again the functions are nonnegative moduli restricted
to the real line. Theorem2's trigonometric weighted derivative estimate has
an absolute c_2 and degree factors; Theorem3 is on (−1,1). These weights
are generalized products with positive exponents, whereas the literal
polynomial reformulation above uses a negative-power weight. This body does
not provide a direct exact bridge either. The earlier survey was also read
in the root lane; its stated absolute-constant bounds agree with this scope.

For u(θ)=|f(e^{iθ})| away from zeros,
|u'(θ)|=u(θ)|Im(e^{iθ}L)|, whereas
|f'(e^{iθ})|=u(θ)|L|. Bounding the first does not bound the second.
Even an unspecified sharpness-in-order assertion cannot replace the required
constant. No full literature clearance follows from inspecting these papers.

## Fresh registry/source screen, and access limits

Live HTTP refresh: omega head825c45ec540a33564ceff35e4e368ddc0e95f6ae,
committer2026-10-29T03:44:23Z. Complete Problems1531, D512430,
Blueprint22996 entries, all truncated=false. Their complete path-to-blob-SHA
maps have zero differences from the supplied Jacobi final-review evidence
(the older head there is675300b0287b26d66ca7920962c26a21fc2ff4ec).
OpenAI head7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a,
committer2026-10-26T21:18:03Z; preprints13578 entries, truncated=false,
zero differences. Current CONTENTS was fetched and screened too.

Target terms were screened in paths and catalogue, not every theorem body.
Bergman algebra entries, Erdos covering/digit entries, and Mersenne
RationalPower paths are not title/path matches to this target. This does not
certify that an inconspicuously named theorem cannot subsume it. No actual
full prior proof was identified, so no chronology-based exclusion is asserted.
The bounded web queries in search-log.json found the original source and
neighbouring polynomial literature, not a verified full solution.

Fresh arXiv history still gives v2,15Jan2024 as latest. Published JAT301(2024)
106048/DOI10.1016/j.jat.2024.106048 body remains unread: the recorded publisher
403 was respected and not retried. No claim that thesis introductory PDFs
contain appended article bodies; the known34/100/102-page limits remain.
No new lawful full journal copy was located in this bounded search.

The runtime HTTP receipt clock reads2026-10-29 UTC while task environment
current_date says2026-10-28. Receipts retain the observed runtime timestamps
verbatim; no date backdating or inferred public chronology is used.

No formalization was started because the full mathematical endpoint is absent.
No PROOF.md is offered as if these reductions resolved the source problem.
