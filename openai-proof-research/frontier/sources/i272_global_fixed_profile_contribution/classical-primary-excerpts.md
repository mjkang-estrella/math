# I272 short primary transcriptions and reading notes

These are short mathematical transcriptions and original paraphrases of the primary extents actually read. Temporary full-text reading extracts were removed. They are not full papers or substitutes for the read extents in literature.md.

## Carlen–Frank–Lieb

Primary: https://arxiv.org/html/1301.5032v2 . Read all Sections 1–2 and 5, including presented proofs. Theorem 2.2(i), for p=gamma+d/2<=2, controls the normalized scalar lowest-eigenvalue loss by a positive multiple of

    inf_(W in M) ||V_- - W_-||_p² / ||V_-||_p².

Theorem 5.1 controls normalized scalar GNS loss by squared H¹ distance to its optimizer family. Lemma 5.3 is local; the proof of 5.1 uses compactness of minimizing sequences to exclude a sequence outside the local neighborhood. This is scalar methodological precedent, not matrix full-moment stability.

## Leng

Primary: https://arxiv.org/html/2606.03749v1 . Read the spectral introduction through Theorem 1.2 and its discussion; Section 2 through its proof, including Lemmas 1–4. With s=gamma+d/2,

    P_V=V_-^s/integral V_-^s,

Theorem 1.2 controls normalized scalar lowest-eigenvalue loss by a positive multiple of inf_W ||P_V-P_W||_1². The method combines a probability-density Hölder remainder with CFL. The orientation in a matrix rank-one projector is not an input to this scalar density.

## Read–Schulz

Primary: https://arxiv.org/html/2609.10478v2 . Read the entire introduction and all mathematical Section 2, including the complete proofs. Proposition 4 treats finite orthonormal families in H¹(R;H), H a separable complex Hilbert space, and bounds their total kinetic energy below by (pi²/4) integral tr R³. Duality gives (2.1):

    Tr(-d² I_H-V)_- <= [4/(3sqrt(3)pi)] integral tr V^(3/2).

V is strongly measurable, nonnegative compact-operator-valued, with finite displayed cost. This is a gamma=1 operator inequality, not a stability remainder.

## Hundertmark–Laptev–Weidl

Primary: https://arxiv.org/pdf/math-ph/9906013 . Read physical pages 3–8 with intact formula text, including complete Theorem 3.1 proof and Corollary 3.5. For nonpositive trace-class V with integrable negative trace, Theorem 3.1 gives

    sum sqrt(E_j) <= (1/2) integral tr V_-.

Corollary 3.5 integrates shifted square-root moments with a beta kernel, yielding the operator-valued constant 2L_cl at higher exponents. Its exponent lifting is distinct from imposing a fixed largest binding energy and minimizing a sharp soliton cost.

## Frank–Gontier–Lewin

Primary: https://arxiv.org/pdf/2109.05984v2 . Read physical PDF pages 5–10, including all Section 2 statements. Theorem 1 decomposes scalar finite-rank normalized maximizing sequences into spatially separated optimizer bubbles. Theorem 5 classifies scalar gamma=3/2 finite-rank maximizers as normalized KdV multisolitons and gives approach to that manifold. These are scalar spectral-rank statements; neither is the finite-matrix physical orientation comparison under review.
