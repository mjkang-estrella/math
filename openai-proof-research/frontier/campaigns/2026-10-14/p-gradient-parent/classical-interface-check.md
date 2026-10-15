# Supplementary classical interface check

This parent check supplements, and does not rewrite, the completed proof
reviews. It adds no new finding.

## Julin--Juutinen interface

Primary source: [arXiv:1104.2197v1](https://arxiv.org/html/1104.2197v1).
Read the introduction, Section 2, and Section 3 through Remark 3.3 using
the existing PDF text extraction (pages 1--6); compared the introduction
and Section 2 against the live primary HTML on 2026-10-14 (local date).
The extracted file SHA256 is `d9b66761c5381e2bc9d9e98158e37c8c8d1970b1ecbc6e82ff9a069ceb0a4c67`.

For p>=2 the source permits the ordinary viscosity definition. Its
introduction records weak-to-viscosity equivalence as an older result;
Theorem 3.1 proves the converse through p-superharmonicity. Section 2
relates locally bounded p-superharmonic functions to weak supersolutions.
Remark 3.3 supplies the almost-everywhere Hessian convergence used in the
appendix. These are credited classical interfaces, not new deductions or a
re-audit of all cited proofs. No singular-p argument is needed here.

The parent separately verifies the operator identification used for p>=3.
For q!=0, setting epsilon=1/(p-2),

    Delta_p(phi) = (p-2)|q|^(p-4) (X[q]+epsilon |q|² tr X),
    q=Dphi, X=D²phi.

The multiplier is positive. At q=0, the derivative of the flux
q -> |q|^(p-2)q is zero for every p>2, and the polynomial operator in
parentheses is also zero. Thus both inequalities agree at all upper and
lower tests, including the original critical set. The factor |q|^(p-4)
is never evaluated at zero. This observation supplies no quantitative
regularity by itself.
