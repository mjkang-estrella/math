# Several removed neighborhoods: exact localization calculation

This is a diagnostic calculation, not a new nominee. Let X be a connected path-connected source test space. Suppose U is the disjoint union of c≥1 nonempty contractible open subsets, with finitely many components, and use the source compact-support categories. Let d be odd. Finite disjoint additivity and the point calculation give E_d(U)=0. The localization exact sequence therefore gives

    0 → E_d(X) → W_d(T(X)/T(U))
      → ker(E_{d-1}(U)→E_{d-1}(X)) → 0.                (1)

If d≡3 mod4, E_{d-1}(U)=0, so the middle quotient map is an integral isomorphism, even with several components.

If d≡1 mod4, identify E_{d-1}(U)=Z^c by the component signatures. All point inclusions into X induce the same map because X is path connected. The map from Z^c consequently factors through the sum Z^c→Z and the point inclusion Z→E_{d-1}(X). The latter is split injective by the map to a point. Thus (1) becomes

    0 → E_d(X) → W_d(T(X)/T(U)) → Z^{c-1} → 0,

where the last group is the augmentation kernel {(a_1,…,a_c): Σa_j=0}. For c≥2, the vector (1,-1,0,…,0) is in the kernel and exactness realizes it by some quotient Witt class. That class cannot lift to E_d(X). A zero total signature is therefore insufficient for a general simultaneous lift.

This is not evidence that the actual character forms have nonzero obstruction. The compact-carrier construction already has global summands, and equality of its concentrated parts uses only a single bad target value. A compatible construction might also make each boundary component vanish separately, or choose d≡3 mod4. The calculation does not prohibit those options. Its role is to keep an honest relative budget rather than replace the source's one-component integral isomorphism by an unjustified blanket assertion.

The same lesson applies to the original marked-boundary project mechanisms: a residual hyperbolic form, vanishing total signature, or balanced ranks is not a geometric relative realization with the prescribed boundary marking. No old relative target is weakened or renamed here.
