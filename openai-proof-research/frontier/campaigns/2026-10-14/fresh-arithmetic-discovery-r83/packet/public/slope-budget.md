# Integer endpoints in the source195 slope budget

This is a preselection feasibility calculation, not a frozen candidate, contribution rating, independent correctness gate, or nominee. It was developed before any target selection. Its purpose is to test the strongest compatible existing reduction for the apparent improvement from 6H² to 3H². All pinned operations are stipulated. The deductions below were checked algebraically; no finite numerical test substitutes for them.

## Exact setting of the calculation

Use source195 `thm:obstruction`: X is a smooth integral projective complex surface, H is ample and globally generated, h=H²>0, T is the FULL section ring of (X,H), and R is its completion at the irrelevant maximal ideal. Suppose R has a nonzero finite maximal Cohen–Macaulay module M, without a grading assumption and with arbitrary positive rank. Write Delta=K_X²−2c₂(X). The source constructs a finite model g:W→V over the blowup of C[[x₀,x₁,x₂]], a smooth Cartier X⊂W with ideal J, D=P²⊂V with ideal I, J=g*I, J|X=O_X(H), and a torsion-free E with torsion-free restriction P. Off D, g_*E is trivial of rank N=rh, where r=rk(P). These constructions, rank identities and all needed extension/exactness operations are already paid by source195 §§2–3. They are not new work of this round.

The normalized slope is mu(G)=c₁(G).H/(rk(G)h). Set

    b=K_X.H/(2h)+3/2,
    m(G)=c₁(f_*G)/rk(f_*G)=mu(G)−b,
    v(F)=2ch₂(F)/rk(F)−(c₁(F)/rk(F))².

Source `lem:factor` bounds v(f_*G)≤c for each nonzero torsion-free H-semistable G, where c=1/4−Delta/(12h). Its Riemann–Roch, Bogomolov and Hodge-index operations and the exact variance mixture identity are all available inside the stipulated proof.

## First compatibility: choose the interval, rather than only its width

The source `lem:balance` performs E' = ker(E→i_*G) on the last HN quotient and supplies exactly

    0 → G(H) → E'|X → B → 0,
    mu(E'|X)=mu(P)+rk(G)/r.

Twisting E by an integer power of J shifts all slopes by that integer and preserves its punctured restriction. First make mu_max(P)<b+1. If mu_min(P)<b, take the last quotient G. Then mu(G(H))<b+1 and mu_max(B)<b+1, so the same extension inequality preserves the strict upper bound. Each step increases the average by at least 1/r. Since the average remains below b+1, there can be only finitely many steps. The terminal HN slopes lie in [b,b+1). This uses neither a prescribed HN filtration throughout the process nor semistability of P. All ranks and the off-divisor trivialization are preserved.

This is the fixed-interval operation in [Chen, 2609.24142v1](https://arxiv.org/pdf/2609.24142v1), Lemma3.1 and Proposition3.3, whose full displayed proofs were read. Chen prints [3/2,5/2); the proof works with any real offset b with no new geometric operation. Here the source already supplies the needed torsion-free version, so no external reflexivity or proposed later cohomology theorem is imported. The arbitrary offset is a parameter of the same termination argument. In the normalized pushforward coordinates, every m_i therefore lies in [0,1).

## Second compatibility: use the integer hinge already present in the layers

Source `lem:lattice`, `eq:layers` and `eq:Tor` give, after an integer twist,

    c₁(F)=T=sum_j n_j,
    2ch₂(F)≥sum_j(2j+1)n_j,
    0≤n_j≤N,

with only finitely many nonzero n_j and j≥0. No splitting of F or graded descent of M occurs. For a=floor(T/N), subtract the affine hinge:

    sum_j(2j+1)n_j − [(2a+1)T−a(a+1)N]
      =2 sum_(j<a)(a−j)(N−n_j)+2 sum_(j>a)(j−a)n_j ≥0.

Consequently, with theta={T/N},

    v(F)≥theta(1−theta).

Integer twists preserve v and the fractional part of c₁(F)/N; thus the inequality applies to the original F too. The bound uses precisely the source's layer capacities and degree inequalities, not an extra property of the quotient layers. It is the minimum of a scalar linear functional under those capacities, attained by filling the earliest slots. In particular, it is not a new sheaf realization theorem or a majorization statement about unprovided subbundles.

## The same pushforward satisfies both estimates

For the modified P let G_i be its actual HN factors, w_i=rk(G_i)/r and m_i=m(G_i). Exact finite pushforward and source `eq:mixture` give

    m=sum_i w_i m_i ∈ [0,1),
    v(f_*P)=sum_i w_i v(f_*G_i)+Var_w(m_i).

Apply the sharpened layer inequality to THIS g_*E and THIS f_*P. Since m∈[0,1), its fractional part is m. Therefore

    sum_i w_i v(f_*G_i)
       ≥m(1−m)−Var_w(m_i)
       =sum_i w_i m_i(1−m_i)≥0.

Combining this with v(f_*G_i)≤c yields c≥0, equivalently Delta≤3h. The calculation is uniform over arbitrary M, rank, HN length and denominators; no limiting, local-in-slope, large-rank, semistable, graded, or subsequence replacement was made. Constants depend only on the displayed intersection numbers. No effectiveness or new construction of M is asserted.

The whole compatibility is explicit: one chosen b aligns the same HN factors with integer endpoints; every elementary transform preserves the same punctured trivialization; that trivialization supplies the layer budget for the resulting pushforward; and its mean is exactly the mean used in the variance identity. There is no independent choice of a new model or incompatible pushforward hidden between estimates.

## Strongest primary and historical comparison

[Anghel, 2609.15589v1](https://arxiv.org/pdf/2609.15589v1), Theorem1.1 and §2 Lemmas2.1–2.4, already gives Delta≤3h for arithmetically Cohen–Macaulay bundles/graded modules. Its full §2 proof uses finite projection, Horrocks splitting, HN slopes and majorization/Karamata; it does not authorize replacing an arbitrary completed-local module by a graded module. That shortcut is unnecessary here. Source195 already replaces splitting by arbitrary Cartier lattices; Chen already fixes the interval; the hinge above uses the stronger numerical information in those very layers. This is an affirmative compatible reduction for the entire scope considered, not a dismissal by naming its pieces elementary or by finding a similar title.

The actual I28 body already compares Anghel and Chen and proves the finite-model transfer for full filtered section rings at the source's 6h bound. The actual large I31 body constructs a nonconical filtered example with all-order gluing, every-degree section lifting and an intrinsic Euler obstruction. Replacing 6 by 3 in those old interfaces or applying the same calculation to their supplied model does not construct a new deformation mechanism. Their author judgments do not decide this round; their operations are the exclusions.

Chronology: initial feasibility considered rotating a width-one interval and an averaged circular-variance estimate. Before selection, the stronger fixed-interval primary was read and the source's exact layer identity was optimized as above. I28's primary comparison and I31's stronger constructed body were followed before any freeze. No theorem statement was frozen at any stage, and no late comparison was backdated.

At Delta=3h the displayed inequalities force every m_i=0. Thus P is semistable and equality holds in the factor budget. This alone does not classify X, produce a flat/projectively flat structure across the exceptional divisor, or split the Cartier extension. Rank-zero layer defects can carry codimension-two information invisible to these first-Chern estimates. A geometric equality classification would require that additional information. It was not closed, not frozen, and not replaced by a semistable or graded assertion. No impossibility of such a classification is claimed.

No nominee is supplied from this calculation. In particular, the stronger numerical conclusion is not itself evidence of an unpaid integrated operation. This is an author preselection disposition only; it assigns no contribution or correctness rating.
