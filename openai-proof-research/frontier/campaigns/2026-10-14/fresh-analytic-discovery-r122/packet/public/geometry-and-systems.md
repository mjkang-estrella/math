# Finite-cone, matrix, and kinetic screens

These are prefreeze comparisons. No author contribution rating or complete extension theorem is asserted.

## 150: from triangles to a fixed finite polygon

The source's exact `thm:main` is weak mixing for every nondegenerate Euclidean triangle with an irrational angle relative to (pi). The actual geometry, energy, rigidity and conclusion sections were read, not only this statement. The same-family ergodicity companion was subsequently read in its geometric/smoothing setup and complete long-average rigidity/conclusion passages.

The operative analytic facts are a compact flat double with finitely many cone points; embedded flat disks of radius at least (c,d(x,V)); (operatorname{Area}\{d(x,V)\le C\epsilon\}=O_C(\epsilon^2)); rotational chart transitions; radial spatial smoothing; and commuting local horizontal fields (X,Y). The coefficients are sections of flat unitary line bundles, so their phases cancel in the energy identities. Source `lem:energy` telescopes spectral terms over consecutive angular indices. `lem:bounded-modes` controls each coefficient gradient without presupposing square summability of all gradients.

The two-limit operation is essential. With (T=s/\epsilon), the bad-segment estimate is (O(s+\epsilon^2)). At fixed (s), smoothing gives bounded exact local eigenfunction solutions and passes the endpoint pairing using the coefficient bounds available at that stage. The exact equation then gives a new coefficient estimate independent of (s), allowing the second limit (s\downarrow0). The separate angular-tail pairing yields

\[
 \|Xf\|_2^2+\|Yf\|_2^2\le\lambda^2\|f\|_2^2,
 \quad Xf=i\lambda f,
\]

and hence (Yf=0). Neither a false initial transverse regularity assumption nor an interchange of the two limits is needed: the source has paid that operation.

For a fixed bounded simple polygon with finitely many positive-angle vertices, the evident geometric substitutions preserve finite cone area and fixed embedded-disk constants. The interior equations still give a plane wave (c(v)e^{i\lambda x\cdot v}). Taking an irrational vertex as origin, its two incident reflections rotate (c) by an irrational angle and force it to be constant almost everywhere. A side whose supporting line does not pass through that vertex then excludes (lambda\ne0). A bounded nondegenerate polygon cannot have all side lines through that vertex. This examines the full combination of analytic and reflection operations, not just individual elementary pieces.

No new compatibility operation was identified in that substitution. A complete theorem for all polygonal domains, including topology and all degeneracies of its precise domain class, was not formulated or proved. No stronger mixing, rates, arbitrary curved billiards, or unrestricted flat-surface spectral classification follows from this scratch comparison.

Forni–Moll, [arXiv:2510.18128v1](https://arxiv.org/pdf/2510.18128v1), Theorem 4.1 and Corollary 4.2, were read with their proofs. Theorem 4.1 concerns the horizontal/holonomy foliation; Corollary 4.2 uses a horizontal Sobolev hypothesis on the invariant function. The source's two-limit proof supplies regularity not available from that primary statement alone. The primary's general finite-cone geometry is an antecedent, but its abstract was not treated as a theorem of weak mixing for measurable billiard eigenfunctions. The rest of its cohomological-equation construction was not read. Primary and companion checks followed initial finite-cone feasibility, before any freeze.

## 365: arbitrary matrix rank and global bundles

The local source proof has more general algebra than a rank-two headline suggests. `mat:spanning` chooses enough harmonic solution jets and uses the smooth right inverse (T^*(TT^*)^{-1}). It keeps the equation constraint on the trace of each Hessian; it does not presume arbitrary unconstrained jets. The comparison identities preserve ordered matrix products. A candidate general-rank projection is

\[
 q_r(Z)=Z-\frac{\operatorname{Re}\operatorname{tr}Z}{r}I_r.
\]

The scalar direction is removed before the conformal-Killing-type system is prolonged. The crucial `mat:finite-type` lemma is already stated for an arbitrary finite-dimensional real vector space (V). Its cubic symbol injectivity for base dimension at least three, finite-dimensional left inverse, and prolonged differential inequalities do not use a Pauli-matrix identity. `mat:improvement` uses this actual prolongation, not a rank-specific commutation shortcut. `mat:local` closes the shrinking-radius argument by openness/closedness and then uses constrained jet spanning to identify the first-order coefficients.

After this feasibility inspection, the actual r118 `geometric-screens.md` was read. It had already made the same arbitrary-(V)/rank observation and distinguished a missing complete global theorem from a new local finite-type operation. This late antecedent is decisive for avoiding a renamed rank variant; its author's verdict is not being adopted as a correctness gate.

For global bundle topology, Gabdurakhmanov–Kokarev, [arXiv:2112.13419v2](https://arxiv.org/pdf/2112.13419v2), constructs Green-kernel bundle embeddings. The setup and Lemmas 3.1–3.3 were examined, with the actual proofs of fiber injectivity, point separation and immersion in Lemmas 3.2–3.3. They use arbitrary-rank bundle test sections and the singular Green equation to rule out identities between distinct points/tangent vectors. Their analytic unique-continuation environment is explicit. Those proofs are not a general smooth unknown-metric continuation theorem, and the full global proof of Theorem 3.4 was not read here.

No complete arbitrary-rank/nontrivial-bundle extension was assembled. Unknown zeroth-order potentials also bring the already recorded conformal gauge issue, not a new inverse problem solved by rank substitution. The exact local algebra and the global analytic primary should both be credited in future work.

## 362: finite-species feasibility, partial reading

Source `thm:global` concerns one species with (f_0\ge0) smooth compact phase-space support, (E_0,B_0\in C_b^\infty\cap L^2), the divergence constraints and no background charge. Its exact one-species normalization was read. Only the initial occupation decomposition and the signed-force cancellation proof were followed in depth, not the entire global closure.

In `can:identity`, the source rewrites the retarded force along receiving and source characteristics, retaining its sign before estimating. The cancellation is a geometric identity involving the normalized velocities, cone denominators and an initial-label measure; it is not a bare positive bound on each field term. The occupation section organizes dyadic momentum/angular ranges under one global momentum cap and conserved positive energy. A finite species label with fixed masses/charges would appear to change constants and relative-velocity normalizations in several of these operations, rather than create an independent cancellation. But the exact source/receiver acceleration coefficients, total work, weighted cutoff sums and continuation criterion were not checked through the entire multispecies proof. Thus this is neither a theorem nor a demonstrated all-species compiler.

The actual r30 `screen-362.md` was followed in the finite-support-versus-tail discussion. It had already isolated the use of a global momentum cap and the difficulty of infinitely many momentum shells for large Schwartz data. A finite-label calculation does not solve that tail problem. No primary multispecies proof was acquired or read in this round, and no priority clearance is claimed for this partial screen.
