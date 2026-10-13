# I274: logarithmic ball–slab point contact

Parent hypothesis and analytic route, 2026-10-12. **Unproved candidate; no count increment.** This differs from the I249/I263 circle-contact problem in contact dimension and predicted energy scale. No independent gate is assigned yet.

## Exact target

On the unit cubic flat three-torus, fix R in (1/(2pi),1/3). For epsilon>0 small let

    A=4pi R^3/3, B_epsilon=2(R-epsilon),
    L_R(epsilon)=inf{P(E)+P(F)-4pi R^2-2:
                    E subset F a.e., |E|=A, |F|=B_epsilon}.

The infimum runs over all finite-perimeter pairs, without symmetry or graph assumptions. The proposed asymptotic is

    lim_(epsilon down to 0) |log epsilon| L_R(epsilon)/epsilon^2=2pi.   (H)

The constant is predicted to be independent of fixed R. No assertion uniform at the endpoints is made. A limsup route is outlined below; neither it nor the full lower bound is certified by an independent review.

## Source and branch check

Read the actual pinned family-354 Theorem intro:main in `frontier/sources/i269_nonlinear_contact_proof/354-paper.tex`, lines 54–84. Its scalar profile and classification are stipulated true at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Since R<1/3, the inner volume is strictly on the ball branch. Since 2R>1/pi and 2R<2/3<1-1/pi, the outer volume is strictly on the slab branch, including when it exceeds 1/2 (use the complementary slab classification). Both separate deficits are nonnegative. The limiting nested scalar optimizers are a radius-R ball centered halfway between the faces of a width-2R coordinate slab. They touch at two poles.

The limiting pair has free boundary patches away from those poles. The two-volume correction and scalar quasiminimality mechanism verified in I269 is a plausible starting point, but its exact adaptation and all subsequent analytic steps must be proved for this new target. I269 does not validate (H).

## Predicted upper coefficient

Fix a small chart radius delta and a positive fixed margin eta. Put a_epsilon=sqrt(epsilon)|log epsilon|. Around each pole on the sphere, and the corresponding point of the adjacent flat slab face, choose logarithmic cutoffs equal to one for rho<=a_epsilon and zero for rho>=delta. On the intermediate annulus use

    chi_epsilon(rho)=log(delta/rho)/log(delta/a_epsilon).

Smooth the two corners with negligible relative Dirichlet cost, keeping chi nonnegative. In a flat chart the leading energy is computed directly:

    integral |grad chi_epsilon|^2 = 2pi/log(delta/a_epsilon).

Move the sphere inward at both poles by amplitude t=(1+eta)epsilon/2 and each slab face outward by the same amplitude. At either pole the relative gain is (1+eta)epsilon. Near each pole the unperturbed separation grows quadratically in transverse radius. Since a_epsilon^2/epsilon tends to infinity, the original spherical curvature pays the gap outside the core disk; inside the core disk the imposed strict margin pays it. A complete proof must control the normal-to-vertical graph conversion in this statement.

The integral of each cutoff is O_delta(1/|log epsilon|). Correct the inner volume by a smooth adjustment away from the poles of size O_delta(epsilon/|log epsilon|); correct the total slab volume similarly. These have Dirichlet energy O_delta(epsilon^2/|log epsilon|^2) and do not affect the leading term. Their effects on contact are absent if supported on free patches, or smaller than the fixed eta margin. Exact volume corrections should be made by a finite-dimensional inverse function theorem, not a merely first-order calculation.

For each of the four surface patches the perimeter energy has leading factor one half times amplitude squared times cutoff energy. Summing gives

    4 * (1/2) * t^2 * 2pi/log(delta/a_epsilon)
       = pi(1+eta)^2 epsilon^2/log(delta/a_epsilon)
       ~ 2pi(1+eta)^2 epsilon^2/|log epsilon|.

The spherical chart metric tends to its Euclidean value as delta tends to zero; its zeroth-order Jacobi term is lower order because the cutoff L2 norm squared is O_delta(|log epsilon|^-2)+O(a_epsilon^2). The slab has no Jacobi potential. Send epsilon to zero first, then delta and eta to zero. This predicts the upper coefficient 2pi. This is an analytic construction plan, not a claim that all its geometric and smoothing details have been checked.

## Lower-bound route and unpaid steps

Use exact paired minimizers, scalar classification and compactness to get a centered ball inside a width-2R coordinate slab in the limit. Adapt the common-flow/lattice argument to obtain scalar quasiminimality and global C1-small normal graphs. The sphere and the two flat tori have coercive Jacobi forms after their mean and translation modes are handled; the slab volume constraint couples the two face means. The expected upper bound would then imply a centered H1 norm O(epsilon/sqrt(|log epsilon|)), rather than O(epsilon).

In transverse charts near the two poles, write the sphere and each slab face as vertical graphs at the SAME transverse coordinate. Actual inclusion should yield the two inequalities

    relative_gap_+(x) >= epsilon+h-|x|^2/(2R)+controlled_errors,
    relative_gap_-(x) >= epsilon-h-|x|^2/(2R)+controlled_errors,

where h is the relative axial translation. Transverse sphere translation can be removed by a common translation because the limiting slab is transverse-translation invariant. The treatment of center modes, reference changes, and the exact remainder on disks of radius c sqrt(epsilon) is not yet proved. C1-smallness alone does not justify an error o(epsilon) after arbitrary coordinate changes; this is a central point to resolve.

One needs a sharp local two-dimensional capacity inequality for an H1 function whose disk average is constrained at radius c sqrt(epsilon), while its outer trace/average is controlled by the global centered H1 norm. Its leading Dirichlet cost should be

    2pi * (constrained average)^2 / log(delta/(c sqrt(epsilon))).

This follows heuristically from radial averages and Cauchy–Schwarz with integral_a^delta dr/r. It must be proved with the correct outer-mean errors, curved metric, and disk-average normalization. Point evaluation is NOT a continuous H1 trace in dimension two and must not be used. The obstacle must supply a disk-average constraint before capacity is applied.

For the relative gap between two surfaces, the elementary inequality

    (1/2)(|grad u|^2+|grad v|^2)>=(1/4)|grad(v-u)|^2

then predicts, after summing the two poles,

    L_R(epsilon) >= [pi+o(1)]*((epsilon+h)^2+(epsilon-h)^2)/|log epsilon|
                  >= [2pi+o(1)] epsilon^2/|log epsilon|.

The argument must also show that the centering/outer-mean errors are o(epsilon), or control them without presupposing the target asymptotic. The global H1 bound is smaller than epsilon, which is encouraging, but local vertical-coordinate conversion and mean coupling remain to be justified. Negative spherical Jacobi terms cannot simply be dropped; their contribution must be shown lower order or absorbed with a loss tending to zero. A fixed coercivity constant is insufficient to recover the sharp coefficient.

A possible way to handle the last difficulty is a fixed spectral cutoff. After kernel and volume modes are dealt with, split the sphere graph into finitely many low spherical harmonics and its high-frequency remainder. For each fixed cutoff, the low part is uniformly O(epsilon/sqrt(|log epsilon|)) and hence o(epsilon), so it should not change the contact constraint at leading order. Its Jacobi energy is nonnegative. On the high part the negative L2 term costs only O(1/cutoff) of the Dirichlet energy. Send epsilon to zero before sending the cutoff to infinity. This remains a proposed argument: one must pay the nonzero graph mean and all changes to the two contact constraints explicitly.

## Status and required review

The coefficient and scale are a new hypothesis within this project, supported by an explicit capacity calculation. A bounded search of actual iteration reports found no previous ball–slab/point-contact nomination under those terms; this does not prove no related prior work exists. No external capacity or constrained-isoperimetry literature has yet been screened for (H), and no novelty claim is made.

Next work should attempt the full nonlinear lower bound and complete the upper geometry, then obtain independent proof and contribution reviews. If the lower argument cannot handle coordinate errors or the negative Jacobi terms sharply, retain (H) as unresolved. Neither a formal linearization nor the logarithmic cutoff calculation alone is an accepted finding.
