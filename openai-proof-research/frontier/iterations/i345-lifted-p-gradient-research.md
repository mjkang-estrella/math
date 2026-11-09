# I345 — lifted, constrained actual-p gradient research

2026-10-13. **Verdict: completed unrestricted theorem candidate, requiring independent proof and contribution review.** The I344 outline was tested rather than accepted as an axiom. One proposed comparison needed repair; the repaired estimate still closes the argument. No acceptance, publication, count increment or index change is made.

## Exact result

For each integer n>=2 there exist alpha_n in (0,1/3] and C_n<infinity such that every bounded weakly p-harmonic u on B1, for every finite p>=3, satisfies

    ||Du||_infinity(B1/2)+[Du]_{C^{0,alpha_n}(B1/2)}
        <= C_n osc_B1 u.

Use the continuous representative of the weak solution. There is no nonvanishing, quasiconcavity, boundary regularity, or assumed gradient-continuity hypothesis. The exponent is nonexplicit. The full proof and internal-input revalidation are in [analysis.md](../experiments/i345_lifted_p_gradient_research/analysis.md).

## What was validated

1. Kotschwar–Ni's actual Theorem 1.1, with w=-(p-1)log v and Euclidean curvature zero, has |Dw|=O_n((p-1)/R). Dividing and shifting a signed solution to M<=v<=2M gives a p-uniform local Lipschitz bound. This is an application of classical prior art.
2. Expanding-domain value compactness gives entire globally Lipschitz p_* or infinity limits. Entire p_* limits are affine by classical regularity/scaling; entire infinity limits are affine by the stipulated infinity estimate/scaling. Original dimension two is covered by the exact infinity lift to dimension three. This proves uniform qualitative Euclidean flatness and then cylinder flatness, without borrowing the source's infinity three-point argument for p-solutions.
3. U(y,b)=u(y)+b solves its correct modified equation

       H[DU]+epsilon |Pi DU|^2 tr(Pi H)=0,
       epsilon=1/(p-2), Pi=I-e_b tensor e_b.

   A regularized Schur-complement test proof includes zero original gradients and zero vertical test curvature. The lift is not claimed p-harmonic.
4. The source's geometric cylinder selection and extraction apply once qualitative flatness and the lift's nonzero total fitted slopes are proved. The new PDE passage uses continuous elliptic extensions that agree on every physically constrained test jet. A single bounded quadratic contact proves that negative effective viscosities have nonnegative limiting lower bound.
5. At finite effective viscosity the added-coordinate constraint gives V=k s+W on a perpendicular space. Both the anisotropic trace and rank-one Hessian term reduce to the isotropic fitted equation. The fits project exactly with the same C0; no enlargement or slope bound is needed. The zero-viscosity source Liouville theorem and the independently revalidated finite-positive-viscosity I236 theorem force affinity.
6. At infinite effective viscosity the modified lifted polynomial, extended with max(B,0), satisfies Savin's global ellipticity and uniform local smoothness/ellipticity assumptions. Its zero-jet spatial block is I-aa^T, and its time Schur complement is exactly one. The amplitude family gives proportional C2 estimates, not just absolute regularity.

## The repair to I344

The source's quadratic norm comparison is for **equal fitting parameters**. I344 compares a base Lambda lambda fit to a coarse eta=kappa lambda fit without paying the first unequal-parameter comparison. The quoted O(eta(1+log nu)) estimate does not follow directly from that lemma.

An independent common-axis argument supplies

    |c_coarse-c_base|
       <= C[kappa^2 lambda+eta(1+log nu)].

At the initial unequal-parameter pair, the common inscribed ball gives direction error O(kappa sqrt(lambda)); a common axial segment of length comparable to r/sqrt(kappa) gives the quadratic norm error O(kappa^2 lambda). Subsequent dyadic comparisons use equal eta and contribute O(eta log nu).

This weaker estimate is enough. With A_base=nu lambda/epsilon and kappa=64(4nu^2)^gamma,

    |A_coarse-A_base|/A_base
       <= C epsilon [kappa^2+kappa(1+log nu)]/nu ->0.

Thus coarse A is positive and comparable to base A. Strengthened running maxima supply the actual domain through H=nu^2 r and a fit at eta/e_coarse->0. The lifted Savin cylinder estimate has fine-scale error C e_coarse r^2/H=o(lambda r), contradicting the chosen bad fit. A vector-only comparison would not pay this transfer.

## Consequence and limits

The common power cylinder-flatness bound gives alpha=gamma/(2+gamma) and the unrestricted gradient estimate. For normalized locally value-convergent p-solutions with a common oscillation bound, finite differences then give

    ||Du_p-Dv|| <= C ||u_p-v||^{alpha/(1+alpha)}

on nested interior balls, when v is the infinity-harmonic limit. This is a consequence, not another nomination. No unconditional value rate or boundary estimate is asserted.

The result is substantive relative to the project's I230/I241 restrictions: it removes original critical-point and selected-slope hypotheses. It depends on the stipulated OpenAI infinity theorem and Liouville theorem; it does not audit their truth. Kotschwar–Ni, Uhlenbeck, Savin, weak/viscosity equivalence, and divergence-form Harnack are primary antecedents. A bounded literature comparison does not establish worldwide priority. The parent must still commission independent full proof and contribution gates before acceptance.

## Assigned evidence

- [Analytic proof](../experiments/i345_lifted_p_gradient_research/analysis.md)
- [Reading and failed shortcuts](../experiments/i345_lifted_p_gradient_research/reading-and-failures.md)
- [Input authentication](../experiments/i345_lifted_p_gradient_research/input-authentication.json)
- [Literature and source interfaces](../sources/i345_lifted_p_gradient_research/literature.md)

Only these four files and this report were written. No subagents, git operations, numerical scans, saved full external bodies, earlier-evidence edits, shared-index edits, or live-sibling reads were used.
