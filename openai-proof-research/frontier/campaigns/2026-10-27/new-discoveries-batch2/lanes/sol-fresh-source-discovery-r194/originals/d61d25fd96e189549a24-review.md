# T212M independent full-scope proof-correctness review, round 1

Reviewed packet: `frontier/campaigns/2026-10-14/fresh-analytic-discovery-r74/`
(author manifest SHA256 `26a78331dfff175abd747c1b4212e48f5c9b24d703702d0474549dbd2eaf9566`,
78 manifest files; author bytes unchanged by this review). The pinned
OpenAI source (source212 at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`) is
accepted as true. AH = Ahlberg–Hoffman arXiv1609.02447v2, DH = Damron–Hanson
arXiv1209.3036v1, both read in the packet's extracted text. The parallel
`t212m-parent` directory was not read.

## Verdict

**PASS_FULL_T212M**

Target checked: for every nonatomic Borel probability G on [0,∞) with finite
values, iid weights on the edges of Z², almost surely there is no bi-infinite
geodesic, simultaneously over all paths, with no moment and no prescribed
direction. The quantifiers follow along the author's chain:

* "every nonatomic G": bounded support is inside source212's class
  (01-introduction.tex:24–37, minimum-of-four second moment); unbounded G is
  handled by the cap route, whose band choice (candidate §2) is valid for every
  such G (checked: a<M strictly, all four band masses positive, ε<1/512).
* "simultaneously over all paths": candidate §3 gives pathwise equality of the
  geometric t- and s-bigeodesic sets on one event; the final contradiction
  (§7) excludes all cap bigeodesics on one event using only countable
  collections of selectors, radii, sites, unions and partitions.
* "no moment, no direction": every moment, shape, Busemann and structural
  statement is made for the cap metric s (all moments); every probability
  kernel is an original-iid or status-preserving kernel on (t,V). No original
  moment or direction is introduced.

**REQUIRED objections: none.** Optional items are listed separately below.
This verdict concerns proof correctness of the frozen author packet only. It
is not a contribution/novelty verdict, formalization, acceptance, or count
change.

## Chain re-derived by this reviewer (dependency-map order)

C1–C3 cap core (candidate §3). Re-derived: L_e≥10 (3×2 rectangle) so
K_e≥M·L_e³≥2ML_e. A t-bigeodesic crossing a changed edge e must enter and leave
C_e; the part between outermost contacts costs ≤ML_e/2<K_e<t_e, contradiction.
The replacement induction (both outside / one inside / both inside, the last
using that γ[a,b] lies within γ's outermost-contact segment of cost ≤ML_e/2)
strictly lowers the changed-occurrence count without raising s-cost, giving
s-minimality of t-bigeodesics. Converse uses s≤t on unchanged edges. Rays from
x use changed edges only in the finite E_x. Finite influence: L'_e=L_e for
remote e, and upward original changes give L'≥L, K'≥K, s'≥s. Conditional
independence/nonatomicity of s given statuses gives unique finite paths.

M shape (§4, cap-author-shape-and-length.md, cap-shape-interface.md). Local cap
s^R≤s with radius-O(R) dependence, residue-class Hoeffding (R⁷ loss) and
R=⌈log(n+2)⁴⌉ summable; cheap-long-path counting through s≥min(t,M); Kingman
with factor-of-iid mixing; fixed-event good-center extension. Supplies AH
Prop 3.4 and A2(vi) for s.

E nonergodic extension (stationary-extension-cocycle.md and the parent
snapshot). Two-sided axis Birkhoff limits, global invariance by Borel–Cantelli
from integrable T_s(0,w), conditional bad-center densities on the invariant
σ-field, per-component N after pre-intersecting deterministic N. Valid for the
AH9.2 extension without inheriting cap mixing.

D DH coupling (dh-limiting-coupling.md, structural-author-bridges.md). DH A2/A2'
hypotheses for s verified against DH lines 145–180 and A2 in AH 331–336. DH
Theorem 1.1 is stated under A1 or A2 (DH 205), so Sections 3–5 and Cor 4.7
(DH 1151) do not use upward finite energy; that enters only at DH Section 6.
Domination: the modified X' has density ∏_{e∈F}1{t_e>a}/r ≤ r^{-|F|}, so
graph pushforwards satisfy ν'≤Cν uniformly in α and n, which survives the joint
weak limit. Stability of an entirely uncapped limiting ray avoiding F:
strict margins t_e<K_e (probability-one), monotonicity, tight change radius R
and no-return box S, then exact unique-minimizer preservation of the whole
finite point-to-line path; Fatou bound ≤2ε. Checked.

O/W wall (cubic-wall.md). Axis: crossings of x=−1/2 at heights 1..m−1 closed ⇒
vertical span ≥m ⇒ L'≥2m ⇒ K'≥8Mm³ > H_m; raised s'>H_m. Diagonal: blocked
crossings are consecutive half-integers −2m−1/2..2m+1/2 ⇒ u-span >4m. Unchanged
open outer circuit of O(m²) edges is cheaper for large m. Corridor entry from the
left requires a rung or meets an outer root. Least element in lexicographic
order contradicts AH Lemma 9.11 mass transport, transferred by ν'≤Cν (DH graph)
or by absolute continuity of X' (AH selectors). Positive probability of the
joint event uses r=G((a,∞))>0 (unbounded G) and a≥H_m chosen after m.

Point mass and references (candidate §5(d)). See Scrutiny 1 below for tangent
coverage. AH5.3–5.6 quantile extraction plus AH4.4 identification make the
conditional limiting graph law a point mass at G_ρ; this is a ν-full event of
(X,graph), hence ν'-full, so the new graph is G_ρ(s(X')). Stability then gives
coalescence of old/new reference rays under the explicit (X,X') coupling.

A AH6–8 with 8.6 replaced (same-status-lowering.md). Single-original resampling
within its M-status freezes every L and changes only that cap edge. Usable
uncapped ray edges (H_o or H_c) get decrement ≥g with probability ≥p_*.
AH's ε,δ are fixed from A2 before v and P1–P3 (AH 8.6); the replacement fixes
δ=g/2 from the bands first, matching that order. F_n-conditional reversibility
and the displayed inequality with C1, C2 → 1 exclude P(A)>0. A2(vi) and
(vii)(b) are supplied by §4 length bounds and iid usable-edge counting.

P/9.5–9.10 (label-stability-interface.md, ah-9-10-integration.md). See
Scrutiny 3. Common good prediction site: ergodic density of bad predictors
≤η per marginal, transferred by absolute continuity; union ≤2η<κ inside the
unaffected cone. Symmetric application, squeeze by AH6 label monotonicity,
isolated-label endpoint convention, and AH9.5(b) via AH9.9 plus a no-return
box. Each step re-derived.

S/Z classification (AH §10, ah-9-10-integration.md). 10.2, 10.5–10.12 use 9.1,
reference linearity, extended shape and countable nets; no finite energy. 10.9
is an all-ray statement on one event. 10.11 fixed-ρ null sets are not
intersected uncountably (source212 02-preliminaries.tex:162–172 respects this).

H half-plane transfer (§6, parent-author-halfplane-transfer.md). Independent
splice of (t,V); changed-vertex bound z₂≤−n+3+max(L_e(X)+L_e(X_n)); diagonal
subsequence for A_n(X_n)→0 in probability; last-changed-vertex suffix with
exactly shared costs; source04 lemma cut-transfer and independent-exceptional
hypotheses (V_n, W_n independent, each with the cap law) are met.

B/T/F budgets, forks, tilts (§7, parent-author-status-preserving-perturbations.md).
Hidden-low posterior p_as/r_s; λ_h integrates to one with second moment
1+δ_h²Σ_s(1/p_as+1/p_bs); posterior θ_e=Σ_s 1_{H_s}(Y_e)δ_h/(p_bs+δ_h)
(recomputed from the raise mechanism); cap gain ≥g because the output
bigeodesic is uncapped (Y_e≤K_e) and K is unchanged under status-preserving
raises; distinct-marks and p/8≤q_m≤ℓW_I/m with p,ℓ,W_I fixed before m.
Source212 02-preliminaries.tex:242–248 transfers almost-sure assertions to
absolutely continuous environments; here absolute continuity is on (t,V) and
pushed to s. Source212 03-sectors.tex contains no probabilistic step
(no independence, resampling, ergodicity or translation argument).

## Points placed under scrutiny and how they resolved

1. **Theorem 10.8 needs Theorem 5.2 for every tangent functional.** AH defines
   ρ as *tangent* when {ρ=1} is the unique supporting line at some point of
   ∂Ball (AH 267–269). Uniqueness of the supporting line at x is exactly
   differentiability of ∂Ball at x, which is DH's hypothesis (DH 200–203,
   1149–1153). So for each tangent ρ, the DH construction at such an x has
   deterministic slope ρ (DH Cor 4.7), and §5(d) covers every member of the
   set used in AH 2897–2898. Corner supporting functionals that are not
   tangent are not required by 10.8 (AH 286–288; AH 3895 leaves them open).
   Not a gap.
2. **AH Thm 5.1 is stated with half-plane targets, the author uses DH rounded
   lines.** AH Lemma 5.3 and the quantile construction 5.4–5.6 use only the
   properties (a)–(d) of a translation-invariant limiting law (AH 792–798,
   824–849), not the target shape. DH's line convention yields those properties
   for s (with (b) from the new coupling). Not a gap.
3. **Replacing AH Lemma 9.6 before 9.7.** AH 9.7's proof uses 9.6 only to
   conclude that Γ_i(z)(ω) and Γ_i(z)(ω') coalesce, then coincide by unique
   passage times (AH 2241–2242). The author obtains exactly this for the
   upward original coupling from the point-mass identification and the
   uncapped-ray stability claim. Proposition 9.5 is only needed in its
   (b) form under ω≤ω' for 9.10's wall (AH 2389–2399), which is the coupling
   used. Not a gap.

## Optional (non-blocking) items

O1. ah-9-10-integration.md line 78 and candidate §5(d) say "choose a
differentiability point". State the quantifier explicitly: for each tangent
ρ, choose a point of ∂Ball where {ρ=1} is the unique supporting line.

O2. Candidate §5(d): say explicitly that after the point-mass step, the
stability statement concerns the explicit law of (X,X') and not the chosen
subsequence.

O3. label-stability-interface.md lines 139–150: state that new realized labels
lie in L_* by absolute continuity of the new marginal, since that is what makes
"new label > β implies ≥ α" valid.

O4. cubic-wall.md (lines 3, 56–59, 116–134) keeps its historical "NOT proved"
selector premise. The discharge is in label-stability-interface.md lines
88–103 and dh-limiting-coupling.md lines 37–107; the dependency map could cite
these lines next to the wall.

O5. Constants differ harmlessly between the diagonal note (H=Mm³, K'≥64Mm³)
and candidate §5(c) (4Mm³). Any threshold exceeding the O(Mm²) circuit cost
and below K' works.

O6. The source212 Appendix (09-boundary-comparison.tex) is cited only as an
alternative to AH Lemma 4.6's boundary-expectation step. AH 4.6 applies to s
directly because s has every moment, so the appendix is not needed.

## Residual limits

The reviewer accepted, without re-reading every line, the proofs inside DH
Sections 3–5 and AH Sections 4, 6, 7 and 10 whose hypotheses were checked at
statement level and whose finite-energy use sites were located by reading;
see reading-limits.md for exact ranges. No numerical or formal checker
certifies infinite-volume steps. The included verifier checks only byte
identity and verdict/record consistency.
