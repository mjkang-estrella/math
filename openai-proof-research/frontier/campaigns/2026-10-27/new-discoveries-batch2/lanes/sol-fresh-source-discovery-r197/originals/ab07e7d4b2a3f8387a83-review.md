# Contribution / prior-work audit r1 — full stable CRT cut theorem G

Reviewer role: independent contribution sub-agent, round 1.
Author of the reviewed candidate: Myeongjin Kang, no affiliation.
This review: original prose CC BY 4.0; reviewer check code MIT.
Private third-party materials retain their rights.
Date: 2026-10-16. Directory: `fk-stable-cut-contribution-r1/` only.

## 0. Verdict

**TECHNICAL** for the entire unchanged target G.

G is not a duplicate of any statement I found. No pinned OpenAI manuscript
and no primary statement I read asserts a trace-norm limit of an all-edge
heavy-tailed barrier Green operator on a conditioned tree or map. But each
operation of the proposed bridge reduces, by substitution, to a named primary
result or to an elementary operation:

1. **Exact finite reduction.** On a tree, the mean-zero Green operator is the
   sum over edges of $R_e\,u_e\otimes_m u_e$. On a map, the cut-vertex (series)
   decomposition adds a positive term per nonloop block. Both are classical
   and already credited to F (candidate lines 112–115, 693–694).
2. **Interval-location cut measure (4.3).** Abraham–Delmas–Nassif (ADN)
   already code each subtree above level $r$ through the straddling
   excursion interval $[T^-_{r,s},T^+_{r,s}]$ and integrate
   $\int ds\int_0^{H(s)}dr\,f(\sigma_{r,s},\dots)$ (ADN §6.1 and (6.17)). The
   candidate replaces a function of the interval length by a Lipschitz
   function of the interval endpoints. The coarea identity (4.6) is ADN
   (1.8)/Prop. 3.2. The 0–1 link thinning is a direct application of the
   source bounded-label path theorem, which the candidate itself uses as a
   black box (lines 108–110, 208–216).
3. **Poisson stable marks.** Pareto marks exceeding $\varepsilon b_N$ occur
   with probability $\varepsilon^{-\alpha}N^{-1/2}$. They are an independent
   Bernoulli thinning of a measure that already converges by item 2. The exact
   Laplace product (6.2) is the standard Bernoulli-to-Poisson passage. In one
   dimension, Faggionato's random-barrier theorem (Thm 2.5, proved in §9)
   uses exactly this mechanism: Poisson marks with Pareto tails replace the
   Lebesgue scale function by a stable subordinator.
4. **Operator continuity and the two trace tails.** Since
   $\|1_I-1_J\|^2=|I\,\triangle\,J|$, finitely many rank-one terms depend
   trace-norm continuously on their marks. The small-mass, small-mark and
   large-mark remainders form the standard three-cutoff truncation for Poisson
   series with stable intensity. Their only model input is the subtree-power
   expectation bound (3.3)–(3.4), at the Fill–Janson scale $N^{a+1/2}$.
5. **Cyclic second-moment payment.** The two-path $\alpha$-moment (7.3) is F's
   mechanism: an edge cut of size two doubles the Pareto tail exponent. The F
   contribution review classified that mechanism as standard. The
   selected-child identity (3.5) is the cyclic lemma followed by the
   first-passage (Kemperman / Otter–Dwass) convolution for a $(k-1)$-forest.
   The resulting $E[\xi^2;\xi>K]$ cost is the size-biased many-to-one count
   $E[\xi g(\xi)]$ with $g(k)=k1_{k>K}$. Combining them in (7.6) is a
   one-line subadditivity and Markov estimate.
6. **Injectivity and domains.** Dense span comes from a laminar, separating
   family of clade indicators plus the monotone-class theorem. The domains
   $\mathrm{Ran}\,K$ and $\mathrm{Ran}\,K^{1/2}$ come from the compact positive
   spectral theorem. Both are routine.
7. **Normalization.** The identity
   $2n(2n+1)^{1/(2\alpha)}/n^{1+1/(2\alpha)}=2(2+1/n)^{1/(2\alpha)}$ is exact.

Taken together, the limit object has a short description in the candidate's
own terms. If the link resistances are set to one, the candidate's Sections
4–6 applied to the link (bridge) part alone, at $a=1$ and scale $M\sqrt N$,
give the deterministic cut operator $c_q\int u_x\otimes u_x\,\ell(dx)$. (With
unit resistances everywhere, the cyclic blocks would not be negligible at that
scale; the comparison concerns only the bridge part.) G replaces $\ell$ by a Poisson stable random
measure with control measure $c_q\,\ell$. This is the tree analogue of
Faggionato's one-dimensional barrier substitution. The branching geometry
comes from ADN and the source, and the tree series identity turns the
spectral step into trace-norm continuity. The conditional trace law (5.4) is
a positive $\alpha$-stable law whose random scale $J_e$ is an ADN/Fill–Janson
additive functional with $f(s)=(s(1-s))^\alpha$.

The remaining unpaid content is the specific assembly, the endpoint-coded
version of the ADN measure, and the bookkeeping that every cyclic block costs
only $E[\xi^2;\xi>K]$. That content is real and could be publishable as a
careful technical result. It is not a complete nonroutine bridge by the
campaign standard ("complete nonroutine theorem; no inflated count for
technical corollaries").

**This is not a proof PASS.** I did not audit correctness beyond what the
contribution assessment needs (Section 7 lists items noticed in passing; they
do not bind the proof gate). I did not read the parallel proof audit
`fk-stable-cut-proof-r1/`. **No worldwide novelty or priority certificate is
given or implied.** The contribution verdict concerns G exactly as stated. If
G is proved, its contribution is TECHNICAL. If the proof fails, the proof gate
governs.

Why not the other verdicts:

* **Not DUPLICATE.** I found no statement of G or of a theorem specializing
  to it. ADN, Fill–Janson, Croydon, CHK, Faggionato, Archer and Andriopoulos
  differ in model, regime, clock or conclusion (Section 4).
* **Not UNRESOLVED.** Every component of the nominated bridge has an explicit
  reduction above. The cutting/pruning literature (Section 6, O10) is unread.
  It could add antecedents for the marked measure, but it cannot move the
  verdict toward SUBSTANTIAL.
* **Not SUBSTANTIAL.** No step requires a new idea beyond the composition
  "ADN coding measure + bounded-label thinning + Poisson stable marks + tree
  series identity + F's cyclic tail + size-biased counting". The candidate
  explicitly excludes the analytically harder companions: a process limit,
  resistance-form/Dirichlet-form construction, heat-kernel or spectral-dimension
  statements, and a law for $\|K\|$ (lines 66–67, 350, 617–619).

## 1. Exact scope assessed (unchanged)

The verdict applies to G exactly as fixed in `original-scope.md` (SHA256
`d8686a39…34a6`) and `candidate.md` §1 (lines 13–78, SHA256 `5c339f83…7144`):

* Every real $q>4$ and every $\alpha\in(1/2,1)$; every integer $n\ge1$.
* Rooted spherical $n$-edge FK map with weight
  $q^{k_M(A)+(|A|-|V(M)|)/2}$; loops and parallel edges retained.
* Iid Pareto $R_e$ on **every** edge, $P(R>r)=r^{-\alpha}$, $r\ge1$.
* Original-degree clock $m(v)=\deg_M(v)$ (two darts per loop), generator
  $L_nf(v)=m(v)^{-1}\sum_{\text{nonloop }e=vw}R_e^{-1}(f(w)-f(v))$,
  $K_n=(-L_n)^{-1}$ on degree-mean-zero functions ($0$ for one vertex).
* $M=2n$, $N=M+1$, $b_N=N^{1/(2\alpha)}$, preorder corner-cell pullback $U_n$.
* Exact source offspring law, $\sigma^2=\mathrm{Var}\,\xi\in(0,\infty)$,
  $c_q=p_2/\sigma$; Poisson intensity $c_q\,\ell(dx)\,\alpha r^{-\alpha-1}dr$.
* Joint convergence in law of
  $(\sigma H_N/(2\sqrt N),\,(Mb_N)^{-1}U_nK_nU_n^*)$ to $(e,K)$ in
  $C[0,1]\times$ trace norm on $H_0$, with the same $e$.
* Well-posedness, positivity, trace class, nonzero, injectivity, the inverse
  domain $\mathrm{Ran}\,K$ and form domain $\mathrm{Ran}\,K^{1/2}$, top inverse
  eigenvalue finite, positive and nonconstant, and
  $n^{-[1+1/(2\alpha)]}\tau_n\Rightarrow2^{1+1/(2\alpha)}\|K\|$.
* Not included: $\alpha=1/2$, a process limit, resistance-metric compactness,
  a largest-bridge identification, or a Fréchet law.

I checked that the candidate's intensity matches the scope. With
$\theta=p_2/2$ (4.1), the constant $2\theta/\sigma$ in (4.3) equals $p_2/\sigma$.
I also checked that $P(R/b_N>r)=r^{-\alpha}N^{-1/2}$ gives exactly the
intensity $c_q\,\alpha r^{-\alpha-1}dr$ after multiplying by the $N^{-1/2}$
measure (4.3).

## 2. Authentication (hash-only, before reading content)

I ran only inline Python over bytes; no stored candidate code was run.

* `seal.json` SHA256 =
  `13658895e2242a0eb3ecbed3f1910345666d10afc83de4d32befe9a9647585c4`, equal
  to the externally supplied anchor; `seal.sha256` is consistent.
* `inputs-manifest.json`: 111 files; `outputs-manifest.json`: 19 files. All
  sizes and SHA256 values match. Membership is exact: no extra or missing
  files and no symlinks.
* All 13 pinned upstream blobs match their Git blob SHA1 in
  `sources/preprints-tree.json` at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
* The candidate `checks.py` and `verify.py` were neither read nor executed.
  My checks (Section 8) are independent code.

## 3. Reading extents

Line numbers refer to the text extractions in the inventory (Section 10).

| Source | Extent read | Used for |
|---|---|---|
| candidate.md | all 738 lines | object of review |
| original-scope.md, review-brief.md, scope-freeze.json | full | scope |
| source-contracts.md, literature-screen.md, working-math.md | full | candidate's own screen |
| Pinned `trees.tex` | full (1–299) | `tree:excursion`, `tree:conditioning`, `tree:paths`, `tree:spine-law` |
| Pinned `blocks.tex` | 1–60, 180–237 | decomposition, offspring, link/loop marks |
| Pinned `metric.tex` | 1–135 | degree measure, bounded-label path use |
| sources/CONTENTS.md and preprints-tree.json directory names | grep for barrier, Pareto, random resistance/conductance, stable, cut operator | duplicate screen of pinned repo |
| ADN arXiv:2009.08185v1 | 1–420 (Thm 1.1, Rem 1.2, (1.6)–(1.8), Thm 1.3, Cor 1.4, Props 1.5–1.6); 600–940 (Prop 3.2 and proof, Prop 3.3, Lemma 3.4); 1265–1504 (Cor 4.7, Lemmas 4.8–4.9, Cor 4.10, Rem 4.13); 1835–1859 (§6.1 straddling-excursion coding); 2245–2269 ((6.17), Lemma 6.11); 2625–2824 (Prop 7.1 and proof, Lemma 7.2, Thm 7.3) | items 2 and 4 |
| Fill–Janson arXiv:2104.02715v1 | 120–299 (Thms 1.2, 1.3, 1.6, 1.7, 1.10, 1.12; Rems 1.13–1.15) | scale, endpoint, moment hypotheses |
| Faggionato 2012 | 540–599 (Thm 2.5); 2067–2211 (proof, §9) | 1D barrier template |
| Croydon arXiv:1609.05666v1 | 24–153 (Assumption 1.1, Thm 1.2), 1462–1531, 1800–1859 | resistance-space route |
| CHK arXiv:1609.02120v1 | 1460–1669 (§6.1: Assumption 6.1, Lemmas 6.2–6.3, Prop 6.4) | heavy conductances / FIN |
| Archer arXiv:2011.07266v1 | abstract and assumption statements only | decorated stable trees |
| Andriopoulos arXiv:1812.10197v1 | abstract and assumption statements only | Gaussian tree potentials |
| F contribution review and parent corrections P1–P4 (history) | review §0; corrections file in full | campaign standard; prohibited claims |
| Web screen, 2026-10-16 | about 9 queries; title/abstract level only; Yang arXiv:2408.07139 abstract | duplicate screen |

Not read: `fk-stable-cut-proof-r1/`, Aldous CRT III (cited by the candidate
at line 582), and the CRT cutting/pruning literature. Archer, Andriopoulos and
the web results enter only as context at title/abstract/assumption level
(parent correction P3). No verdict step depends on them.

## 4. Operation-level comparison

| Candidate step (lines) | Antecedent operation | Status |
|---|---|---|
| (7.1) block series $K_n=\sum_BJ_BJ_B^*$; link term $R(1_A-s)\otimes_m(1_A-s)$ (453–487) | Classical cut-vertex/series decomposition; tree Green operator $=\sum R_eu_e\otimes_mu_e$ (verified exactly, Section 8) | credited by candidate; routine |
| (3.1)–(3.4) local-limit and subtree-power bounds (121–161) | Janson cyclic fringe identity; Fill–Janson scale $N^{a+1/2}$ for $a>1/2$ (Thms 1.7(iii), 1.10(i)) | credited; the candidate re-derives it under finite variance only, avoiding FJ Thm 1.3's extra moment $E\xi^{2+\delta}$ |
| (3.5)–(3.6) selected-child identity (163–197) | Cyclic lemma + Kemperman/Otter–Dwass first-passage convolution; size-biased count | credited as non-new (670–673); routine |
| (4.2) marked path discrepancy (208–216) | Source `tree:paths`, bounded 0–1 label | direct application |
| (4.4) finite interval coarea (230–247) | Exact bookkeeping (verified, Section 8) | elementary |
| (4.5) endpoint continuity (248–278) | ADN Prop 3.3 continuity via (1.8); ADN §6.1 straddling excursion $[T^-_{r,s},T^+_{r,s}]$ | routine extension from length to endpoints |
| (4.6) coarea on $T_e$ (280–292) | ADN (1.8), Prop 3.2 | known |
| (5.1)–(5.2) unmarked measure; $E\int s^\alpha\ell<\infty$ (305–329) | ADN Thm 1.1(i)/Prop 1.5; Fill–Janson Thm 1.10(i)/1.12 | credited, not nominated (322–325) |
| (5.3)–(5.4) Poisson series; conditional trace Laplace transform (331–350) | Campbell's theorem; positive stable law with ADN-functional scale $J_e$ | routine |
| (6.2)–(6.3) Bernoulli-to-Poisson and finite trace-norm limit (364–386) | Standard Laplace-functional thinning; Faggionato §9 1D analogue | routine |
| (6.4)–(6.8) three trace tails (388–449) | Standard truncation for stable Poisson series; inputs (3.3)–(3.4) | routine |
| (7.2)–(7.7) cyclic blocks (489–543) | F's two-path $\alpha$-moment (Menger + independence); size-biased count (3.6); subadditivity of $x^\alpha$ | credited mechanism; routine combination |
| §8 dense span, injectivity, domains (545–619) | Laminar separating clades + monotone class; a.e. injective coding; compact spectral theorem | routine |
| (1.3) constant (627–632) | Exact algebra | elementary |

Results that do **not** pay G (theorem-level reading):

* **Croydon** Assumption 1.1/Thm 1.2 requires convergence of boundedly compact
  measured resistance spaces. The candidate's limit claims no resistance-metric
  compactness, and Croydon's theorem does not produce trace-norm operator
  convergence from the undisturbed CRT. It is an alternative route, not a
  premise.
* **CHK** §6.1: resistances $\omega^{-1}\le1$ homogenize, and heavy
  **conductances** give a FIN speed measure under the conductance clock. Here
  the heavy objects are resistances (infinite mean) and the clock is the
  original degree. Different regime.
* **Faggionato** Thm 2.5: a segment, not a conditioned branching structure,
  and the limit is a Krein-string generalized operator. It is the template,
  not a premise.
* **ADN/Fill–Janson**: scalar additive functionals and measures on tree
  space. They lack the endpoint coding (though ADN §6.1 carries it), the link
  thinning, the Pareto marks, the operator and the cyclic blocks.

## 5. Answers to the four specific bridge questions

**(a) Interval-location cut measure.** Not a bridge. In ADN, the subtree
above level $r$ containing $x$ is, in coding terms, the excursion of the
height process above $r$ that straddles $s$. Its endpoints
$T^\pm_{r,s}$ are named explicitly (ADN lines 1840–1856), and (6.17) is the
coded coarea integral with a function of the excursion length. The candidate's
(4.5) is the same integral with $F$ a bounded Lipschitz function of the
endpoints. The endpoint-sandwich argument at continuity levels (lines
249–262) is the elementary step that ADN's continuity proof also needs for
lengths. Location adds bookkeeping, not an idea. The marked version uses the
source's bounded-label path theorem as a black box, plus summation by parts
against a bounded-variation weight (lines 237–246).

**(b) Two trace tails.** Not a bridge. Both tails are first-moment or
Laplace bounds for nonnegative sums. The small-mass tail uses
$E(1-e^{-zR})\le Cz^\alpha$ and (3.4). The small-mark tail uses the truncated
first moment $(6.6)$ and (3.3) at $a=1$. The large-mark event uses a union
bound. This is the textbook proof that a Poisson series with stable intensity
is the limit of the thinned heavy-tailed sums. The only model-specific input
is the Fill–Janson-scale expectation bound, which is credited.

**(c) Injectivity.** Not a bridge. Poisson marks are dense on the skeleton
because the intensity diverges as $r\downarrow0$. Clade indicators are
$L^2$-continuous along arcs, are laminar and separate leaves. The
monotone-class theorem gives density. A.e. injectivity of the coding map is
the standard "a non-leaf or an atom" dichotomy (lines 588–595). The
almost-sure, all-$g$ quantifier is handled correctly by working with the span
of a random family (lines 600–603).

**(d) Cyclic second-moment payment.** Not a bridge, although it is the most
model-specific step. The tail mechanism is F's, already classified as
standard. The new part is accounting: with (3.6) and $g(k)=k1_{k>K}$, the
cost is $E[\xi^2;\xi>K]$ rather than a third moment. This is the size-biased
child count. Also, (7.5) uses the crude bound $\sum_w|T_w|\le N\max H$. One
paragraph suffices for an expert.

**Do (a)–(d) form a nonroutine bridge together?** No. The package is the
composition described in Section 0, in the paragraph after item 7. Each
interface is a direct match. Item (a) supplies exactly the measure item (b)
needs. The tree series identity turns that measure into the operator. Item
(d) is an independent positive remainder. Item (c) concerns only the limit
object. No interface requires a new estimate beyond those listed.

## 6. Line-specific objections

Severity scale: **Critical** would change the verdict; **Major** affects the
contribution disposition or framing; **Moderate** affects crediting;
**Minor** is editorial or a screen gap. No objection is Critical.

* **O1 (Major), lines 227–228, 678–680, 705–707.** "Preorder interval
  location" is listed as part of the proposed full bridge. ADN §6.1 (lines
  1840–1856) and (6.17) (lines 2252–2256) already code subtrees by the
  straddling excursion interval and integrate the coded coarea. The
  candidate's step is a substitution of the integrand (endpoints instead of
  length), with ADN Prop 3.3-type continuity. Recommendation: credit the
  coding to ADN §6.1 and remove location from the nominated bridge.
* **O2 (Major), lines 696–698.** Faggionato is called an antecedent that
  "does not include the conditioned branching geometry and cyclic payment".
  This understates the reduction. The branching geometry is supplied by ADN
  and the source. On a tree, the series identity replaces Faggionato's Krein
  spectral continuity by trace-norm continuity of finitely many rank-one
  terms plus tails, which is simpler. The cyclic payment is F's mechanism.
  Recommendation: state that G is the conditioned-tree analogue of the 1D
  stable random-barrier substitution, and assess what remains.
* **O3 (Moderate), §§5–6 and 10.** The candidate never states the
  deterministic analogue. Unit resistances on the link (bridge) part give,
  via (4.3) at $a=1$ and the same cutoffs, the limit
  $c_q\int u_x\otimes u_x\,\ell(dx)$ at scale $M\sqrt N$. G's bridge part is
  the Poisson-stable subordination of that object; G's cyclic part is a
  negligible remainder only because of the heavy-tailed scale. This
  identification is my derivation; it is the continuum form of the exact
  finite identity verified in Section 8. I did not read a primary statement
  identifying it with a Brownian-CRT Green operator, so I make no citation
  claim. Recording it would make the contribution boundary transparent.
* **O4 (Moderate), lines 163–197, 194 ("Most importantly"), 670–673.** The
  selected-child identity is the cyclic lemma plus the hitting-time
  (Kemperman/Otter–Dwass) convolution, and the $E[\xi^2;\xi>K]$ cost is the
  size-biased count. The candidate credits it as non-new, which I endorse.
  The emphasis at line 194 should not be read as a bridge claim.
* **O5 (Moderate), lines 489–506, 693–694.** The two-path $\alpha$-moment is
  F's argument verbatim, already classified as standard in F's contribution
  review. (7.6) adds only subadditivity and Markov's inequality at the new
  scale $(Mb_N)^\alpha\asymp N^{\alpha+1/2}$.
* **O6 (Minor), lines 116–119, 322–325, 674–677.** The credit to Fill–Janson
  is accurate. Note for the record: FJ Thm 1.3 (lines 146–155) needs
  $E\xi^{2+\delta}<\infty$. The candidate does not use it as a premise and
  re-derives (3.3)–(3.4) under finite variance (lines 126–161). This is
  correct crediting, not an objection to the proof.
* **O7 (Minor), lines 343–350.** The conditional trace law (5.4) is a
  positive $\alpha$-stable variable with random scale
  $c_q\Gamma(1-\alpha)J_e$. Here $J_e$ is an ADN-type additive functional
  (ADN (1.8) with $f=(s(1-s))^\alpha$). It is worth saying that the trace
  marginal of G is immediate from ADN/FJ plus Campbell's formula.
* **O8 (Minor), line 582.** Aldous CRT III §2.3/Cor. 22 is cited. I did not
  read it. The self-contained argument at lines 585–595 suffices for the
  contribution assessment.
* **O9 (Minor, editorial), lines 46, 54, 357–358.** Line 46 and the frozen
  scope define $u_x$, but (1.2) at line 54 writes $\nu_x\otimes\nu_x$;
  $\nu_I=1_I-|I|$ is defined only at line 358. These are the same vector.
  Unify the notation.
* **O10 (Minor, screen gap), §10 and `literature-screen.md`.** The screen
  omits the CRT cutting/pruning literature (for example Aldous–Pitman,
  Abraham–Delmas pruning, Janson's random cutting, Bertoin–Miermont cut
  trees). There, edge marks at rate of order $N^{-1/2}$ on conditioned GW
  trees converge to Poisson marks on the CRT skeleton with intensity
  proportional to $\ell$. I did not read these at theorem level and do not
  rely on them. They can only add antecedents for item 2/3, so they cannot
  turn the verdict SUBSTANTIAL. A future screen should check whether any of
  them states a located version of (6.3).
* **O11 (Observation, scope; parent correction P2).** The parameter $q>4$
  enters only through the source's exact decorated GW representation (block
  marks, $p_2$, $\sigma$). I do not claim, and the verdict does not use, a
  transfer theorem to other block-decorated families.

Consistency with parent corrections: no universal tree-gap comparison is
used or suggested (P1; the candidate preserves the path counterexample at
lines 643–647). No general decorated transfer is asserted (P2).
Title/abstract analogies are context only (P3). Nothing is inferred at
$\alpha=1/2$ (P4; candidate lines 649–652).

## 7. Items noticed in passing (non-binding for the proof gate)

These are spot checks made only to understand the operations. They are not a
proof audit.

* Scale bookkeeping: $(Mb_N)^\alpha=M^\alpha N^{1/2}\asymp N^{\alpha+1/2}$
  matches (3.6). (7.5) is $O_P(LN^{3/2})$ against $Mb_N\asymp
  N^{1+1/(2\alpha)}$ with $1/(2\alpha)>1/2$. (6.7) uses
  $E\sum_ws_w=O(N^{1/2})$, giving $C/\delta$. (6.6) follows from
  $E[R;R\le t]\le\frac{\alpha}{1-\alpha}t^{1-\alpha}$ and $b_N^{-\alpha}=N^{-1/2}$.
* The $M$ factor at lines 484–487 is consistent: $\otimes_m$ is $M$ times
  the tensor for the probability mass $m/M$. My tree check (Section 8) uses
  nonuniform degree masses including loop darts.
* (7.6) uses that block shapes and corner resistances are independent of the
  child subtree sizes given the offspring number. This is the source's
  independently marked GW representation, as the candidate states (lines
  92–96, 508–510). The proof gate should confirm the conditioning at the
  near-$N$ boundary, which (3.5) handles exactly.
* I did not check the endpoint-sandwich argument (4.5) at the level of a
  proof audit. In particular, I did not check the one-cell
  preorder-versus-interpolation errors or the uniformity of dominated
  convergence. These belong to the proof gate (review-brief item 2).

## 8. Independent reasoning and exact checks

`reviewer_checks.py` is written independently and uses exact `Fraction`
arithmetic. It was run with `python3 -B`. The receipt is
`reviewer-checks-receipt.json`. It is finite support only, not a proof of any
limit and not a contribution verdict.

* **(a) Tree Green operator = sum of cut rank-ones.** On 40 random trees
  with 2–8 vertices, degree masses plus random extra loop darts, and random
  rational resistances, $(-L)^{-1}$ and
  $\sum_eR_e(1_{A_e}-s_e)\otimes_m(1_{A_e}-s_e)$ agree exactly on three
  random $m$-mean-zero test functions per tree. Result true. Control: using
  vertex-count masses instead of degree masses is rejected.
* **(b) Selected-child identity (3.5).** Brute force over all plane trees with
  offspring law $\{0:5/8,\,2:1/4,\,4:1/8\}$, $N=3,5,7,9,11$ (1, 3, 11, 46 and
  207 trees), with $g(k)=k^2+1$ and $F(s)=s^2+3s$. Exact equality in every
  case, including $s=N-1$ and empty remainders. Control: shifting the lattice
  site $1-k$ by 2 is rejected.
* **(c) Preorder interval coarea (4.4).** On all 61 trees with $N\le9$, with a
  nonconstant 0–1 label and a polynomial $\phi$, the identity
  $\sum_wb_w\phi(I_w)=\int dt\sum_{w\preceq v(t)}b_w\phi(I_w)/s_w$ holds
  exactly. Control: omitting the self term is rejected.
* **(d) Nested-cut example (§9).** Both weights are 1; trace 2; determinant
  $2/3$; normalized squared inner product $1/3$. This matches the candidate's
  characteristic polynomial $\lambda^2-2\lambda+2/3$.

Reasoning not checked numerically: the reductions in Sections 0 and 5, the
deterministic analogue in O3, the constant identities in Section 1 and in
item 7 of Section 0.

## 9. Limits of this review

* This review gives no proof PASS and does not replace `fk-stable-cut-proof-r1`.
* It is not a worldwide novelty or priority certificate. The screen is
  bounded (Section 3), and web results are title/abstract level only.
* No manuscript, Lean, upload, message, commit, staging, shared-index edit or
  sibling edit was made. No nested agents were started. The frozen r9
  directory was not modified.
* The verdict is for the whole package G. No supporting lemma or
  reparameterization is assessed as a separate nomination.

## 10. Inventories

### Inputs relied upon (size in bytes, SHA256)

Paths are relative to `openai-proof-research/`; `R9` means
`frontier/campaigns/2026-10-14/fresh-analytic-discovery-r9`, and `UP` means
`R9/inputs/private/frozen-r7/inputs/private/upstream/preprints/Brownian-continuum-random-tree-limits-of-finite-Fortuin-Kasteleyn-maps-above-four-September-24-2026/build`.

| Size | SHA256 | Path |
|---:|---|---|
| 1298 | e9ab951853e1607e8d125adb5609a89214a46bb655fda39874257b8210093e7e | AGENTS.md |
| 179 | 3784eb61f1efa141ed49d00c5d13a5206502c4081759abff4f64c99183b5f30c | sources/upstream.json |
| 638727 | cc7c0b8a1cdedd845a777e77cf682657308503daf8346c1349e06e9259d063c2 | sources/CONTENTS.md |
| 4858136 | eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b | sources/preprints-tree.json |
| 500 | 13658895e2242a0eb3ecbed3f1910345666d10afc83de4d32befe9a9647585c4 | R9/seal.json |
| 76 | 363c8d785ad15c7a90fbdc5f52e24145196de699904d657194f4e9d841a9b567 | R9/seal.sha256 |
| 23105 | b6957d3fb1c8af43a7771b7df9d4a7dc07c38837295b04b0886e09cad850b895 | R9/inputs-manifest.json |
| 2891 | cd9188882b429dc31718303ea504bd142c56056e3b82070e7c102ce35428a8f3 | R9/outputs-manifest.json |
| 38644 | 5c339f83efac52d43965a400ac6b693bb52100475e8ccddcd8ad490897567144 | R9/candidate.md |
| 4167 | d8686a39d756a2aee505382600106c0aa6f821f5a9496016767752038ab634a6 | R9/original-scope.md |
| 239 | 2b9f8321299a5b4914ca2fb8e437fd0fb0a460ae1bf8c4580ba073aa4da0901b | R9/scope-freeze.json |
| 2575 | b0bcd72f7f9fa5ff0093bcc0a842dae7c51ccae33050656d194cc50962e3a9f2 | R9/review-brief.md |
| 8436 | 7a1d19f22374124ca33141be42afc3d3e881526c8513358829dc137928fa2f04 | R9/source-contracts.md |
| 5357 | 08c59ca37b567dbcd409ef589b740814607b20312e136084e3557ee659bb6b79 | R9/literature-screen.md |
| 3369 | 28b4058930df6a4fa8b75ce65ef2e071f2ba14776a4482c71d3876ce4586980c | R9/working-math.md |
| 2166 | 5d86851600ded9e31d9c7d0c7d9032b903a2b4c9b9656bdc3562427287515c91 | R9/literature-retrieval.json |
| 49735 | d5fd3924c67e0f757daf7f79706950eddd60dbd2d8b5f9064521a22a31802930 | R9/input-provenance.json |
| 285796 | 48077d461039e19ec2cae9e0341dec4d90a487490a40458169d31147b16e8ff6 | R9/inputs/private/literature/adn-2009.08185v1.txt |
| 307854 | cf234e45bac41e17b6603c4d5c60d908c61ec5025836583fc21977eadf441a47 | R9/inputs/private/literature/fill-janson-2104.02715v1.txt |
| 127525 | e16e8b0fd17e995deb8b48b703c634ce0206f3424f22bfc4d803a4f413a9713a | R9/inputs/private/literature/croydon-1609.05666v1.txt |
| 162665 | 4ea660fe350093ad13305582e5370524ea47cdceec61602cdcbdb5062dade927 | R9/inputs/private/literature/chk-1609.02120v1.txt |
| 304857 | 7c32e2176622b0d993497becbb128dd431df54e6c2892c654771d0c9845d3c06 | R9/inputs/private/literature/archer-2011.07266v1.txt |
| 103193 | 657d7f56b51e8bb60b23eb89de8d6463434ccdb5e4aef646562dfb8d3df8e890 | R9/inputs/private/literature/andriopoulos-1812.10197v1.txt |
| 152300 | 4d3c8dec5441894257181c43466eba1a4473736641c2c82712b5f5193c7d8ffc | R9/inputs/private/frozen-r7/inputs/private/literature/faggionato-2012.txt |
| 11705 | 630e88b02a17e32be0cc403cd604428c869b87f096233009900c0cd7c651cdd8 | UP/sections/trees.tex |
| 9792 | e92a957aeada0eaef66dd816e672ec87cea6994210d750070ec233ec484795ce | UP/sections/blocks.tex |
| 9881 | e1d6005d60c513e641cad0898f08f42b824e05aee3b9d03439f453b23e0b7842 | UP/sections/metric.tex |
| 24348 | f8ce51e05e34bd69e0fdd6587c584dd05aae436d26c0cac9b5c80b135fea4400 | R9/inputs/private/history/fk-frechet-contribution-r1/review.md |
| 2921 | f6cc32587578b4d735322d1d949a667a7d3e7e00c41ddda3db0e5c2b857de8a4 | R9/inputs/private/history/fk-frechet-parent/contribution-r1-corrections.json |

The Faggionato text is byte-identical (same SHA256) to the copy under
`fresh-analytic-discovery-r7/inputs/private/literature/`.

### Outputs (this directory)

| Size | SHA256 | File |
|---:|---|---|
| 3058 | 41a72fc80310eaae5c66d418740e36dbb0648a0965effc554701f5eb8e241e23 | progress.md |
| 980 | 19af9e245a1b2c647ecc42688c0392b977e869a3bd28d624b14cda1f8da4202b | status.json |
| 8026 | e93ea7d24854f325c01ef917175c2ecf9132d87fd667dd34c691e6ee340bb001 | reviewer_checks.py |
| 540 | b17e72cfa152fd9c2681ee7d2c1c970c0d80e19e192adabcedeeb27115da9474 | reviewer-checks-receipt.json |

`review.md` cannot list its own hash. It is recorded, together with every
file above, in `outputs-manifest.json`. The inputs table is repeated in
`inputs-manifest.json`. `seal.json` binds the SHA256 of both manifests, and
its own SHA256 is detached in `seal.sha256` and the terminal handoff.
