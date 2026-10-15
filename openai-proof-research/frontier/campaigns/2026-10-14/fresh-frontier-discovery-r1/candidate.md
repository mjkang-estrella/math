# Fresh discovery R1: Randers entropy rigidity remains unresolved

2026-10-14. **No substantial theorem is nominated. No acceptance/count change.** The original campaign remains 2/10 on the supplied ledger. This is discovery work, not an independent proof or contribution review.

The complete three-target screen is in `shortlist.md`. The reaction-network and regularized-cone possibilities were rejected after recovering their existing I138/I141 and I198/I200 records. The selected fresh target is geometric dynamics. I attempted the full statement below by two routes. The exact contact reduction and the closed-one-form benchmark are proved here, but the nonclosed-field bridge is not. Neither benchmark nor obstruction is substituted for the original statement.

## Full selected target T

For **every** integer n≥3, every closed connected smooth Riemannian manifold (Mⁿ,g) with strictly negative sectional curvature, and every smooth real 1-form β satisfying

\[
\|\beta\|_{g,\infty}<1,
\]

let F(v)=|v|_g+β(v) be its strongly convex Randers metric. Assume that its unit-speed geodesic flow Φ is Anosov. Let ν_F be normalized canonical contact volume on its unit cosphere bundle. The proposed theorem is

\[
h_{\nu_F}(\Phi_1)=h_{\rm top}(\Phi_1)
\quad\Longleftrightarrow\quad
\nabla^gR_g=0\ \text{ and }\ \beta=df\text{ for some }f\in C^\infty(M).
\tag{T}
\]

All entropies use natural logarithms and the stated physical F-unit-speed time. There is no dβ=0 assumption, no small C² bound, no conformal-class restriction, no assumed negative flag curvature of F, and no prior differentiability of its invariant distributions. The Riemannian conclusion includes real, complex, quaternionic and Cayley hyperbolic universal covers at arbitrary scale. Replacing it by constant sectional curvature would change the claim.

**Outcome:** T is neither proved nor refuted in this assignment. A precise unpaid implication, equivalent to its remaining direction after a proved benchmark, is displayed in (10) below.

## Source dependency and duplicate control

The pin is `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; source theorem truth is stipulated. Source339, *Entropy equality and local symmetry in negative curvature*, `build/main.tex`, `thm:main`, applies to closed smooth negatively curved **Riemannian** manifolds of dimension at least three. Its conclusion is equality of normalized Liouville and topological entropies iff ∇R=0. It does not state T for Randers or magnetic flows.

The main file and complete dynamical preliminaries were read. The exact passage `alg:axis-coherence`, its complete proof, `alg:dichotomy`, the complete ideal-boundary contradiction `real:infinite-excluded`, and the relevant smooth-label geometry were then read to locate the new bridge. No full rereading or automatic extension of every formal-hull proof is claimed. Exact paths, labels, hashes and extents are in the source/read records.

R023 concerns p-harmonic gradient estimates; R024 concerns attained complete-polynomial disk rigidity. The existing accepted statements and recent campaign status were screened. Neither supplies an entropy-rigidity bridge here. The former Cartan–Hadamard, Einstein, Brenier and Crouzeix stability work is not being relabeled. The following contact computations and standard time-change argument are technical controls, not separate proposed frontier findings.

## Exact contact and magnetic reduction, valid also when dβ≠0

Write Σ_g={|p|_g=1} in T*M and let α be the restriction of the tautological form. The dual unit ball for F at x is

\[
B^*_{F,x}=\beta_x+B^*_{g,x}.
\]

Indeed the support function of the translated Riemannian dual ball is |v|_g+β(v); positive strict convexity follows from ‖β‖<1. Translation τ_β(x,p)=(x,p+β_x) identifies Σ_g with Σ_F and pulls its canonical contact form back to

\[
\alpha_\beta=\alpha+\pi^*\beta,
\qquad d\alpha_\beta=d\alpha+\pi^*d\beta.
\tag{1}
\]

Identify Σ_g with S_gM by g. Let X be the Riemannian unit geodesic field, set

\[
r(x,v)=1+\beta_x(v)>0,
\]

and define the vertical vector W_β at (x,v) by its g-normal component Y_β(v), where

\[
g(Y_\beta(v),w)=-d\beta(v,w).
\]

The sign is fixed by dα=d(p_i dx_i). Put Z_β=X+W_β. On tangent vectors to Σ_g, contraction gives

\[
\iota_{Z_\beta}d\alpha_\beta=0,
\qquad \alpha_\beta(Z_\beta)=r.
\]

For example, the horizontal term in the first equation is dβ(v,·), canceled by the vertical term g(Y_β(v),·); Y_β(v)⊥v by skew symmetry. Thus the F-Reeb generator, pulled back to Σ_g, is exactly

\[
R_\beta=Z_\beta/r.
\tag{2}
\]

This is the usual exact magnetic flow followed by a nonconstant time change. It equals X/r precisely when dβ=0.

There is a particularly useful exact volume identity:

\[
\alpha_\beta\wedge(d\alpha_\beta)^{n-1}
 =r\,\alpha\wedge(d\alpha)^{n-1}.
\tag{3}
\]

Proof: a top-degree form on Σ_g must contain n−1 independent vertical covectors, because the fibre dimension is n−1. Every factor π*dβ is horizontal, whereas a factor dα supplies at most one vertical covector. All terms containing π*dβ therefore vanish. For the remaining expression (α+π*β)∧(dα)^{n−1}, evaluate on X and a contact frame. The β contribution on that frame is β(v) times the α contribution; every term using a horizontal β component off X misses a vertical direction. This gives (3) with its exact coefficient.

Let μ_g be normalized Riemannian Liouville volume. Reversal (x,v)↦(x,−v) preserves μ_g and makes β(v) odd, so ∫r dμ_g=1. Consequently

\[
\nu_F=r\mu_g\quad\text{under }\tau_\beta.
\tag{4}
\]

The Reeb field preserves ν_F. Equation (2) then shows that Z_β preserves μ_g: the flux of Z_β against μ_g equals that of R_β against rμ_g. No invariant-measure identification with an incorrect clock is needed. Abramov's time-change formula gives

\[
h_{\nu_F}(R_\beta)=h_{\mu_g}(Z_\beta),
\qquad
h_{\rm top}(R_\beta)=
 \sup_{\eta\in\mathcal M(Z_\beta)}
 \frac{h_\eta(Z_\beta)}{\int r\,d\eta}.
\tag{5}
\]

The invariant-measure bijection is η↦rη/∫r dη. The positive smooth r is bounded above and away from zero for every fixed input, so its time change preserves Anosovness. Actual primary statements of this correspondence, Abramov normalization and pressure transfer were read in Gogolev–Rodriguez Hertz, `Propositions 4.2–4.3`; see the literature record. These are standard tools, not contributions claimed here.

A relevant control is that magnetic Liouville entropy and topological entropy in magnetic time are **not** the pair in T. Even though the first equality in (5) is exact, the second contains the measure-dependent denominator ∫r dη. Thus a theorem about μ_g maximizing entropy for Z_β cannot be applied to T without paying the change of variational problem.

## Complete closed-β benchmark — technical only

Assume additionally dβ=0. Then Z_β=X, so R_β=X/r. The benchmark says that T is true under this extra hypothesis. Its proof is included to isolate exactly the remaining magnetic issue; it is not a nominated narrower result.

Let μ_B be the unique maximal-entropy measure of X. Since X is a reversible negatively curved geodesic flow, velocity reversal carries a maximal-entropy measure to one; uniqueness makes μ_B reversal invariant. Therefore ∫β(v)dμ_B=0 and ∫r dμ_B=1. Equations (4)–(5) imply

\[
h_{\nu_F}(R_\beta)=h_{\mu_g}(X)
\le h_{\rm top}(X)\le h_{\rm top}(R_\beta).
\tag{6}
\]

If T's entropy equality holds, every inequality in (6) is equality. Source339 therefore gives ∇R_g=0, and μ_g=μ_B. Put h=h_top(X)>0. The time-change variational formula implies that μ_g is an equilibrium state both for the constant potential −h and for −hr, with pressure zero in each case. For the latter, for every X-invariant η,

\[
h_\eta(X)-h\int r\,d\eta\le0,
\]

and equality holds at μ_g.

Compare the upper and lower Gibbs estimates for the two potentials on the same Bowen ball centered on a periodic X-orbit γ, followed for k full periods. Their ratio bounds

\[
\left|kh\int_\gamma(r-1)\,dt\right|
\]

by a fixed constant independent of k. Divide by k and let k→∞. Thus ∫_γβ=0 on every oriented closed g-geodesic. This is the same Gibbs/period operation explicitly proved in source `pre:entropy-forms`; it involves only the Riemannian flow X. Every nontrivial free homotopy class has its unique closed g-geodesic, while a closed form has homotopy-invariant periods. Hence β has zero period on every loop and β=df globally. One may define f by path integration from a basepoint; zero periods ensure well-definedness and smoothness.

Conversely, if ∇R_g=0 and β=df, write f also for f∘π on Σ_g and define

\[
\Psi(x)=\phi^g_{f(x)}(x).
\]

Since 1+Xf=r>0, Ψ is a diffeomorphism. On each orbit t↦t+f(φ_t^g x) is strictly increasing and differs boundedly from t; it is onto, and on periodic orbits it has degree one. Its differential is invertible because the orbit derivative is r and its induced transverse differential is that of a fixed-time flow. These facts give global bijectivity and a smooth inverse. Invariance of α yields

\[
\Psi^*\alpha=\alpha+df=\alpha_\beta.
\tag{7}
\]

Thus Ψ strictly conjugates the Reeb fields and their normalized contact measures. Source339's locally symmetric converse proves T's entropy equality. This converse did not require a merely measurable conjugacy or a changed time normalization.

It follows that the remaining full-target obligation is precisely

\[
\boxed{\ h_{\nu_F}(R_\beta)=h_{\rm top}(R_\beta)
\ \Longrightarrow\ d\beta=0\ }
\tag{8}
\]

for every input in T. This is not an additional assumed hypothesis.

## Route A attempted: extend the source's conormal/formal method

The scalar entropy input itself generalizes. For a smooth transitive Anosov flow preserving smooth volume, its unstable-Jacobian potential has pressure zero and the volume is its equilibrium state. If volume is also maximal entropy, Gibbs estimates and Livšic give a constant-plus-flow-derivative identity. Leafwise transfer functions can be obtained by integrating in the contracted time direction. This suggests adapting the source's preliminary conormal construction using unstable determinants and running the stable construction for reversed time, without a Riemannian Riccati graph formula.

That observation does **not** certify the required formal symmetry fields, their coherent jets, or their geometric realization. I inspected the actual source bridge rather than asserting that contact Anosovness is sufficient. Its `alg:axis-coherence` proof uses the velocity flip as an automorphism of the same dynamical system. It preserves the intrinsic plane P′, exchanges its actual stable and unstable parts, and preserves smooth volume. Ergodicity makes their ranks constant; the flip then makes them equal. Since P′ has positive rank, **both** parts are nonzero. The subsequent `real:infinite-excluded` proof requires precisely those two nonzero parts: a proper stable affine ray and a nonzero unstable vector transported along it produce mixed rectangles, contradicted by ideal-boundary geometry.

For a nonclosed β this physical flip is unavailable. Under I(x,v)=(x,−v) on Σ_g,

\[
I^*\alpha_\beta=-\alpha+\pi^*\beta,
\quad I^*\alpha_\beta+\alpha_\beta=2\pi^*\beta,
\quad I^*d\alpha_\beta+d\alpha_\beta=2\pi^*d\beta.
\tag{9}
\]

The reversed magnetic system has field −dβ, not dβ. Repeating the construction for −β compares two systems; ergodicity of either one does not identify the stable and unstable ranks inside the other. Doubling the two systems introduces a nonergodic disjoint union and does not repair that argument.

Nor do symplectic pairing and hyperbolicity by themselves force the missing conclusion. In a symplectic vector space E=E^s⊕E^u with the usual hyperbolic diagonal generator, L=P=P′=E^s is coisotropic and invariant, and has zero unstable part. This elementary example is **not** claimed to satisfy all source formal-Lie-algebra hypotheses. It only prevents a replacement argument based on those elementary properties alone. No full flip-free algebraic lemma was proved.

There are further geometric obligations even if the two-sided formal plane were obtained. The literal source uses uniquely connecting Riemannian geodesics, normalized Busemann functions, smooth horosphere graph bounds, and the uniformly positive U(v)+U(−v) in `smooth:backward-geometry`. The full Anosov Randers hypothesis is not a statement of negative flag curvature, and I did not prove all corresponding endpoint/graph interfaces. No source theorem with Riemannian hypotheses is applied outside them. Route A therefore stops before the mixed-rectangle argument; no general smoothness of E^s,E^u is asserted.

A concrete failure of the automatic-time-change shortcut exists within T's genuine input class. On any closed negatively curved g choose a chart-supported smooth 1-form η with dη≠0 and put β=tη. For all sufficiently small nonzero t, ‖β‖<1 and the Reeb field is a C¹-small perturbation of X, hence Anosov by openness of Anosovness. At a point and direction where dβ(v,·)≠0, (2) has a nonzero vertical component. It is not X/r on the same phase space. This refutes that identification, **not** T or the possibility of a different orbit equivalence.

## Route B attempted: the exact weighted entropy equation

Let J_β denote any Hölder infinitesimal unstable-Jacobian potential for Z_β; changing its reference bundle volume only adds a flow coboundary. Equations (4)–(5), the pressure variational principle and the same Gibbs-period comparison show that entropy equality in T is equivalent to

\[
J_\beta-h\bigl(1+\beta(v)\bigr)=Z_\beta u,
\quad h=\int J_\beta\,d\mu_g=h_{\mu_g}(Z_\beta),
\tag{10}
\]

with a Hölder transfer function u differentiable along the flow. Indeed μ_g is then simultaneously an equilibrium state for −J_β and −hr, both pressure zero; comparison on periodic orbits yields the displayed coboundary. Conversely the cohomology identity makes the two potentials have the same pressure and equilibrium state, so (5) gives entropy equality for the F-clock. This is a thermodynamic reduction, not geometric rigidity.

The exact unpaid statement is that (10), for the full quantifiers in T, forces dβ=0. Source339 supplies the special β=0 geometric rigidity implication, not this new weighted magnetic one. Integrating (10) against μ_g merely gives h=h because ∫β(v)dμ_g=0. It does not give individual periodic integrals of β equal to zero. Differentiating an unknown Hölder unstable-Jacobian potential does not turn it into a tensor of degree at most two on the fibres. Thus tensor tomography cannot be invoked on (10) without a new argument.

The current primary magnetic-action results read concern equality of a **marked action spectrum**, and in higher dimensions their local result assumes solenoidal injectivity plus closeness; their global result fixes a conformal class. T assumes none of those. Entropy equality is not equality of the marked actions of two magnetic systems. No symmetric model, conformal identification, or period-by-period equality with a Riemannian model has been constructed here.

A scalar Riccati/Cauchy–Schwarz shortcut also loses necessary scope. For complex hyperbolic complex dimension m≥2, normalized unstable rates are 2 once and 1 with multiplicity 2m−2. Therefore

\[
(2m-1)\sum\lambda_i^2-(\sum\lambda_i)^2=2m-2>0.
\]

Such a bound is already strict on genuine Riemannian equality examples allowed by source339. It cannot furnish T's full rank-one equality classification. This is a check on the proposed method, not a new spectral theorem.

## Controls, literature and final scope

`exact_checks.py` passed using rational/integer arithmetic: 30 exterior-form/Reeb-normalization fixtures, ten rank-one trace checks and eight elementary one-sided symplectic examples. The all-dimensional proofs of (1)–(9) are the written arguments, not a generalization inferred from those checks. There is no numerical simulation, claimed full Lean formalization, or computation of an entropy.

The bounded primary comparison is in `reading-and-failures.md`, with retained source hashes. In particular, Benoist–Foulon–Labourie's smooth-distribution rigidity theorem does not remove its smoothness hypothesis; modern magnetic marked-action rigidity does not replace entropy by marked data; and one must keep magnetic and Randers clocks distinct. No worldwide novelty claim follows from the searches. The closed-β benchmark is a standard transfer from the stipulated source and established thermodynamic tools and would not meet this campaign's substantiality standard on its own.

T remains open **in this investigation** at (8)/(10), not globally certified open to the literature. A complete proof would have to pay a flip-free magnetic rigidity mechanism (and all its geometric interfaces), or a different argument deriving dβ=0 directly from (10), for every input in T. No smaller parameter class, assumed ergodicity/smooth splitting, fixed real-hyperbolic base, or scalar identity check is nominated instead. All files are confined to this assignment directory; no shared ledger, staging, commit, acceptance or publication action was performed.
