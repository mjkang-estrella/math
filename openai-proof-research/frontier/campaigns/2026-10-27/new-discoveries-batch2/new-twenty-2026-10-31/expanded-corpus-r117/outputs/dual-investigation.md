# MathDB 357870: complete independent computational test, no kernel certificate

Source: Schüler, arXiv:2303.15059v1, Definition 1.1 and Conjecture 2.2. The source's primitive condition excludes both containment in a proper coset and being a union of cosets of a nontrivial subgroup. The MathDB paraphrase omits the second condition. Use the source's scope. The author already reports that a complete graph search terminated with no example and asks for a more readily checkable proof. Reproducing that computation is not automatically a new solution.

Fix the standard pairing (a,b).(c,d) -> exp(2 pi i(ac+bd)/8). Any other isomorphism with the dual group can be absorbed in T. Translations of either set preserve formal duality. Character orthogonality gives |S||T|=64, so if |S|=8 then |T|=8. Thus |chi_h(S)|²=8 nu_T(h) is a nonnegative integer multiple of 8 for every h.

If S is not contained in a proper coset, reduce S modulo 2. Its affine span must have dimension 2: otherwise a nonzero linear functional mod 2 is constant on S, putting S in the preimage of a proper coset. Hence S contains an affine triple o,a,b whose difference columns form an invertible matrix modulo 8 (determinant odd). Translation by -o and the inverse matrix send the triple to 0,e1,e2. Every possible primitive S therefore has a representative containing elements 0,1,8 in the encoding x+8y. The other five points range over all C(61,5)=5,949,147 choices. This normalization need not be unique; uniqueness is not used.

For zeta=exp(pi i/4), express a character sum as a+b zeta+c zeta²+d zeta³ with integer coefficients, reducing zeta⁴=-1. Its squared absolute value is

a²+b²+c²+d² + sqrt(2)(ab+bc+cd-ad).

It is a multiple of 8 only if ab+bc+cd-ad=0 and a²+b²+c²+d² is divisible by 8. Conversely those two tests suffice for this necessary condition. scripts/dual.py applies these exact integer tests for all 64 characters to every normalized set, using vectorized integers. It leaves exactly 78 sets (saved explicitly).

Six of these 78 have nonzero translation periods and are imprimitive. The other 72 have no translation period. They form seven affine orbits, while the periodic six form two more orbits; all nine representative sets and normalized orbit sizes are saved in outputs/dual-orbits.json. No orbit reduction is required for the completeness argument.

For each of the 72 aperiodic sets, compute target[h]=|chi_h(S)|²/8. A hypothetical T may be translated to contain 0. Every other t in T lies in the positive support of target since t=t-0 is a difference. scripts/dual_partner.py recursively lists increasing T with 0 and seven further elements. It rejects a partial T only when an ordered-difference count exceeds target, or when too few remaining points can complete size 8. Pairwise allowed-difference filtering is another necessary condition. Each size 8 leaf would automatically give equality of all difference counts because both sides total 64. The complete enumeration visits 224,081 nodes for all 72 sets and produces no leaf. Per-S support sizes and node counts are saved in outputs/dual-partners.json; full output is retained.

This establishes an ordinary finite verification with a transparent completeness argument. It independently reproduces the source's negative answer. It is not a Lean proof. Missing: kernel formalization of normalization, character orthogonality and the cyclotomic integer test, plus soundness/completeness and kernel replay of both enumerations. A source-code audit alone is not a formal certificate. The source author's prior exhaustive computation also creates a significance issue for a new-credit claim: only a genuinely independently checkable formal certificate, or a substantial structural proof replacing the enumeration, should be considered.

Reproduction, from this lane:

    python scripts/limited.py dual python scripts/dual.py
    python scripts/limited.py dual-follow python scripts/dual_follow.py
    python scripts/limited.py dual-orbits python scripts/dual_orbits.py
    python scripts/limited.py dual-partners python scripts/dual_partner.py

No external compiler, solver or package install is needed. NumPy's arrays use small integer coefficients; the norm calculation stays far below overflow. The six million normal forms are necessary-condition candidates, not six million formal-duality verifications.
