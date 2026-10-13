# I270 — mathematical burden and contribution classification

2026-10-12. **SUBSTANTIAL, as one prospective full theorem.** This analysis evaluates contribution, not proof correctness. It makes no acceptance/count change and does not read the live correctness review. The OpenAI revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` is stipulated true.

## 1. Precise scope and source-dependent geometry

Use $T=\mathbb R^3/\mathbb Z^3$, unit flat metric and De Giorgi perimeter. Fix $2/9<R<1/\pi$; let $a=4\pi R^3/3$, $r=R-\varepsilon$, $b_\varepsilon=\pi r^2$. For small positive epsilon the separate scalar minima are $4\pi R^2$ and $2\pi r$. The inner volume is strictly on the ball branch since $R<1/\pi<1/3$; the outer volume lies strictly on the tube branch since $2/9<r<1/\pi$. Pinned Theorem `intro:main` supplies the exact equality classes.

The proposed minimum asymptotic is

\[
D_R(\varepsilon)=K(R)\varepsilon^2+o_R(\varepsilon^2),\quad
K(R)=\frac{4\pi R}{R+4G_R},\quad
G_R=R^2-\frac R2\cot(1/(2R)).
\]

The class consists of every finite-perimeter nested pair of the two prescribed volumes. At epsilon zero the nested separate optimizers are a ball and shortest axial tube of the same radius. Transverse alignment follows from inclusion of two equal-area projected disks. The axial location of the ball remains free. The contact is the ball's equatorial circle, a codimension-one trace locus in each two-dimensional interface.

The shell volume at the limit is $\pi R^2(1-4R/3)>0$. This is not a vanishing-shell-volume problem. The perturbation is the loss of geometric room for a fixed-volume ball, with all phase volumes of positive limiting size.

## 2. What is already paid, and why it does not imply the limit

Qualitative compactness and the exact equality cases give a positive deficit for fixed epsilon: equality would require the larger-radius ball to fit in the smaller-radius tube. I249 explicitly rejected this as a substantial finding. Its ellipsoid gives an O(epsilon-squared) upper bound; neither positivity nor that upper bound determines a sharp lower coefficient.

Separate quantitative stability supplies squared L1 asymmetry bounds. The aligned radius-$R$ ball loses outside the radius-$r$ tube the volume

\[
\delta(R,r)=\frac{4\pi}{3}(R^2-r^2)^{3/2}.
\]

Thus the elementary compatibility obstruction forces L1 error of order epsilon to the power $3/2$. A squared-error estimate provides only an epsilon-cubed scale. This is an actual failed route, rather than an assertion that classical stability is irrelevant. It explains why a contact trace, capable of seeing a displacement on a measure-zero circle, must replace a purely volumetric argument.

The nested energy formulation is classical. Relabel inner $E$ as phase 2, shell $F\setminus E$ as phase 1, and exterior as phase 0. Interface costs are $\sigma_{12}=\sigma_{01}=1$, $\sigma_{02}=2$. An inner/exterior contact is counted twice by $P(E)+P(F)$. This is the triangle-equality regime. It must not be conflated with the ordinary $1,1,1$ double-bubble perimeter.

## 3. Nonroutine burden of the all-BV passage

The general selection idea is familiar: replace competitors by more regular minima so that an energy comparison reduces a BV inequality to a graph calculation. The problem-specific part is paying for that reduction in the presence of two volumes and inclusion.

I263's common-flow construction uses one field on a free limiting sphere patch inside the tube and one on a free tube patch outside the ball. Their limiting volume Jacobian is invertible. Since volumes of measurable sets are integrals of smooth Jacobians, L1 closeness keeps the correction uniformly available before boundary regularity is known. Applying the same diffeomorphism to both sets preserves inclusion.

For an unrestricted inner competitor $H$, the pair $(H\cap F,H\cup F)$ is nested. Submodularity controls its total perimeter by $P(H)+P(F)$; its summed pair L1 change from $(E,F)$ equals $|H\triangle E|$. Correcting both volumes and comparing with an exact pair minimizer gives a scalar quasiminimality estimate for $E$. The outer comparison uses $(E\cap H,E\cup H)$. The equal coefficients make the cancellations possible. These operations are standard individually; their compatibility removes the particular moving-obstacle obstruction.

AFM's improved convergence is then a classical input. The contribution is establishing the hypotheses for these paired minima, not rediscovering C1 convergence or claiming that arbitrary near-minimizers lack tentacles. Every original competitor is bounded below by the exact minimum, which is enough for the universal lower asymptotic.

This route is short enough to be useful and specific enough to be checkable, but it is not the one-line application of a scalar source theorem. An analogous result under unequal weights, no limiting free patches, singular scalar limits, or several contacts is not supplied or counted.

## 4. Why regularity alone is still insufficient

Qualitative C1-smallness has no epsilon rate. The proposed passage uses exact-volume expansions with errors bounded by a vanishing coefficient times the actual H1 energy. This is the needed form when normalized gradients might concentrate. It avoids assuming a uniform Taylor remainder at a changing smoothing scale.

After removing the sphere's three and tube's two normal translation modes, the Jacobi forms have spectral gaps. The axial cylinder gap requires $R>1/(2\pi)$, satisfied strictly in the assigned interval. Combining those gaps with the O(epsilon-squared) energy upper bound produces H1 graph norms O(epsilon). Means become negligible at the rescaled order through the exact volume constraints.

There is still a coupled normalization issue. Choosing reference centers for each graph does not permit independently moving the actual sets. If their relative transverse displacement is $h$, inclusion at the inner equator yields the proposed exact inequality

\[
\varepsilon+h\cdot e_\theta+\psi(\theta,0)
\leq\eta\bigl(\arg[h+(R+\psi(\theta,0))e_\theta],0\bigr).
\]

This makes the remaining burden explicit: control $h$ at order epsilon, control composition of traces by the small angular reparametrization, and retain the first harmonic in the limiting obstacle. Scalar C1 convergence without a rate does not do that. Adding the limiting spherical translation Jacobi field removes the first harmonic without changing energy. Compact H1 traces into circle L2 are the relevant passage; point evaluation on an arbitrary H1 surface is not being used.

These are the features that make the lower bound substantial. This contribution judgment does not certify every estimate or quantifier in the proposed argument; it identifies the mathematical work that the correctness gate must evaluate.

## 5. The coefficient and recovery within the same finding

Once the compatible trace class is identified, the quadratic task is relatively standard. Common angular averaging discards nonnegative modes, preserving means and the obstacle. For spherical equatorial value $A$ the minimizing mean-zero axial profile is the cusp $A(1-2|t|)$, with half-Jacobi energy $4\pi A^2$. For tube value $D$, the mean-zero period-one Green function of $-d^2/dz^2-R^{-2}$ gives half-energy $\pi R D^2/G_R$. The contact condition becomes $D-A\geq1$.

The elementary minimization

\[
\inf_{D-A\geq1}\left(4\pi A^2+\frac{\pi R}{G_R}D^2\right)
=\frac{4\pi R}{R+4G_R}
\]

explains the precise coefficient. This is a capacity coupling, not just the sum of separate source-profile derivatives. The periodic resolvent remembers the length-one tube, while the cusp encodes the equatorial forcing on the entire sphere.

I249 was explicitly unresolved: this Hilbert-space answer alone did not establish the nonlinear limit. I253 then supplied smooth strict-gap approximants with separately corrected exact volumes. Their positive equatorial buffer dominates O(epsilon-squared) corrections; away from the equator the undeformed geometric gap supplies room. Its order of limits fixes an approximant before epsilon tends to zero. I263's full proposed lower passage makes those earlier pieces one full-limit claim. None receives a separate increment in this review.

The recovery is meaningful, but without the lower passage it remains technical progress. Conversely, a lower bound for smooth coaxial graphs would leave the arbitrary-BV optimization unresolved. The combined statement includes both burdens.

## 6. Strongest comparison and residual obstacle in a standard route

The closest contact-selection comparison located is ABLW Section 4.4. It proves a next-order energy selection of concentric versus tangent core shells and a second Gamma-limit in a two-dimensional droplet regime. This is prior contact asymptotics and must be credited. The source's optimal shells are already composed of perimeter-optimal nested disks; its next term acts on positions through nonlocal interactions. In the present problem, shrinking the tube forces deformation and produces a positive local perimeter cost even with every nonlocal coefficient zero. Transplantation requires the paired graph reduction and trace-capacity calculation above.

A strongest plausible standard-corollary route combines classical volume fixing, perimeter submodularity, scalar improved convergence and constrained second variation. I263 indeed follows that route. What remains substantive before it becomes a theorem is the compatibility of the two-volume correction with arbitrary lattice competitors and the precise rate/contact-trace limit. No read primary theorem takes these hypotheses as an already-solved black box and returns the all-BV coefficient. Calling the work routine solely because its tools are classical would discard the central constrained deduction.

A different possible route uses Milman's BV slice bound twice and nested area profiles. It would still need a sharp expansion with singular parts and disappearing sphere pole slices controlled, plus optimal nonlinear recovery. This review supplies no such alternate proof and no false inference of impossibility.

## 7. Final contribution judgment and presentation repairs

**SUBSTANTIAL** is warranted for the stated full sharp minimum asymptotic, understood as a nonroutine consequence of the stipulated torus theorem and classical tools. The conclusion is bounded by the primary sources actually read and is independent of the unfinished correctness gate. It is neither a proof approval nor a claim of worldwide priority.

Required presentation repairs are to keep one combined theorem, credit every classical ingredient, distinguish minimizing replacement from regularity of every near-minimizer, and describe a limit of minima rather than a full functional Gamma-limit. Use ABLW's actual Theorem 4.5 label for its second Gamma-limit; the introduction's “4.21” is not its theorem label. Do not inflate the proposed theorem into endpoint, flow, many-interface, or general weighted-cluster assertions.

The literature and provenance record disclose unread general shape-sensitivity/contact theories and the bounded search extent. These limits restrict a priority claim, not the demonstrated difference between this theorem and the specific comparisons. No further novelty repair requiring a theorem change was identified at this contribution gate.
