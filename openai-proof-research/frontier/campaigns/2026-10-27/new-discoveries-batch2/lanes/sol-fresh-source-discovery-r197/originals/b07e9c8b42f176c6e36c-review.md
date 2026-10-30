# T027O independent full-proof gate, round 1

Reviewer: independent T027O proof gate (Factory Opus 5.5 lane). Original review prose CC BY 4.0; reviewer scripts MIT. This is a proof verdict only. It makes no contribution, novelty, acceptance or count decision. Campaign count 13/20 and target 20 were given no weight.

## Verdict

**PASS_FULL_T027O.**

Every quantifier of the frozen target in scope027o.md is covered at the unchanged scope:

- for r >= 3 and every g >= 2, by the candidate's own argument, which I rederived step by step below and found complete;
- for r = 2 and every g >= 2, by the cited Coccia–Litt theorem (Proposition 5.0.1 with K = Q(sqrt 5), v = (1+sqrt 5)/2, then Proposition 3.1.10 / Theorem 5.0.2, n = 0 case). The frozen scope expressly credits this case to Coccia–Litt and claims nothing new for it.

I found **no required objection**. The editorial items E1–E6 below are optional or presentation corrections. None of them changes a quantifier, and each is repairable in place without changing the argument. The dependency classes D1–D3 record what the PASS rests on beyond the candidate's own deductions.

There is no restriction to finitely many genera or ranks. There is no generic-input hypothesis, marked or monomial locus, union of orbits, rank-two replacement, or punctured extension. The single orbit is the orbit of rho_0 = (I, B, C, I, ..., I) in SL_r(O_L), with the field depending only on r.

## Frozen inputs and identity

- External anchors, checked before parsing the manifest: manifest.json 2127e23f…f0199, verify.py 2ad360c2…f5e8, candidate027o.md e5812790…8867, scope027o.md 0f53abf3…cda2, source-and-credit.md e1086b79…7391. All five match.
- I read verify.py in full before running it. It walks the inventory, rejects symlinked ancestors, hardlinks, non-regular entries and nested manifests, and compares the manifest bytes with the external anchor before json parsing. Then it checks the exact file and directory inventories, the source-completeness map, the git-blob/SHA256 identities of 13 source blobs, 4 primary bodies with text extractions, and context copies. In place: `python3 -B verify.py 2127e23f…` gives PASS (48 files, 8 directories, 13 source blobs). A wrong anchor gives FAIL. The run left no residue.
- Canonical comparison, independent of the author's selection: sources/preprints-tree.json has SHA256 eeecc1da…5e09b, 13223 entries and truncated=false. It lists 14 blobs under `preprints/Integral-points-on-character-varieties-of-curves-September-25-2026/`. All 13 non-PDF blobs match the author's private copies by git blob SHA-1 and byte length. The only absent path is paper.pdf (blob 61041a8d…, not retrieved, by design). There are no extra local files. Pin: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
- Copied controls ran on disposable /var/tmp copies only, which were removed afterwards. Results are in author-packet-controls.json. The unchanged copy passes. Fourteen mutations fail with the expected diagnostics. Eleven are inventory or anchor mutations: wrong anchor, payload byte, missing file, extra file, extra empty directory, file symlink, root symlink, hardlink, FIFO, nested manifest, and self-reseal under the old anchor. Three are internal-identity mutations under a resealed manifest and a new anchor: a surfaces.tex byte, a primary text byte, and a dropped source receipt. The author packet was not modified or resealed, and its anchor still verifies.

Integrity hashes certify bytes only, never mathematics or novelty.

## Step-by-step rederivation (r >= 3)

**Pisot-unit torus and arithmetic density (§2).**
- Take f = X^r − c0 X^(r−1) − 1 with c0 >= 3. On |X| = 1 we have c0 > 2 >= |X^r − 1|, so Rouché gives r−1 roots inside the unit circle. Since f(c0) = −1 < 0, there is a real root above c0, and it is the unique root outside. A monic factor without that root has a nonzero integer constant term of modulus less than 1, which is impossible, so f is irreducible.
- Multiplicative independence: apply a Galois element moving a root that carries the maximal exponent M to the outside root. Then sum_i (m_i − M) log|sigma alpha_i| = 0, and every term is >= 0. So all m_i = M.
- With eta^r = (−1)^(r−1), the product of the alpha_i is (−1)^(r+1), so the product of the mu_i is 1. The relation lattice of the mu_i is Z(1,...,1), which is exactly the kernel of restricting characters to T. So C_mu generates T densely.
- The set of B(m) is dense: its first r−1 coordinates range over a product of infinite sets, which is dense in (C*)^(r−1), isomorphic to T. Each B(m) generates T: a relation gives m_i(e_i − e_r) = 0, so e_i = e_r.
- SL_r(Z) is dense in SL_r because its closure contains every root group. A product of dense sets is dense in the product. C = Q C_mu Q^-1 lies in SL_r(O_L).

**Simple curves (§3).**
- I recomputed the ribbon structure by hand, with half-edge "x" for the start of x and "x^-1" for its end. The face permutation has one cycle reading a b a^-1 b^-1 c d c^-1 d^-1, so the surface has genus 2, one boundary component, and the standard relator. The same holds for the full genus-g rose order, whose boundary word is the full product of commutators.
- Turn chords are noncrossing with each edge used once. In positions: bd gives {2,8} and {4,6}. abcd gives {3,4}, {2,5}, {7,8} and {1,6}. abcd a_i gives {6,p} and {1,p+2}. abcd b_i^-1 gives {6,p+1} and {1,p+3}. So these based words are embedded.
- The maps b -> b a^m and d -> d c^n fix [a,b], [c,d] and the other generators exactly. For example [a, ba] = [a, b]. So they are boundary-fixing, orientation-preserving mapping classes (powers of the twists about a and c).
- The image of bd under them is u0(k,l). The image of abcd under exponents (k−1, l−1) >= 0 is u1(k,l). The same twists map abcd a_i and abcd b_i^-1 to u1 a_i and u1 b_i^-1.
- Homology classes b+d, a+b+c+d and so on are nonzero, so the curves are nonseparating.
- The twist a -> ab preserves [a,b] exactly: it is the twist about b.
- The obsolete family a^k b c^l d0 is not used anywhere in the proof.

**P1/P2 (§4).**
- P1: at the stated H, (H^2)_12 = H11 + H22 and (H^2)_21 = H11 + H22 + 1, so the determinant is 1. This holds provided the other off-diagonal entries in rows and columns 1 and 2 vanish (see E1). H and H^2 minus its scalar part lie in its eigen-Cartan. Rank two at one pair is a 2×2 minor that is polynomial in Q and Q^-1, so it is an open condition. Relabel by signed permutations and intersect the opens.
- P2: the Laurent-coefficient criterion is correct. The required expressions are regularity (discriminant), the off-diagonal entries and the triangle differences, evaluated on Q T Q^-1. Neither P1 nor P2 depends on mu.

**Principal-minor lemma.**
- I rederived the 3×3 derivative by summing over permutations with E_ab = x_ab M_ab. The identity contributes 0 and the transpositions vanish by x_ij + x_ji = 0. The two 3-cycles give (M_ij M_jk M_ki − M_ik M_kj M_ji)(x_ij + x_jk + x_ki).
- Taking h_i = x_i1 gives E = [diag(h), M].
- For r = 3 the 3-minor is det. Its derivative is automatically zero in both applications: det(NB + eps(XN+NY)B) has derivative det(NB) tr(X+Y) = 0, and det(B(N + eps[R,N])) has derivative 0.

**Residual system (5.1) witness and openness (§5).**
- Take Q real orthogonal with nonzero entries. Then h_C is complex symmetric, and h ∩ h_C = 0 because k_i Q_ij = Q_ij lambda_j.
- Normalized limits K of S_t lie in the centralizer of C, which is h_C. The quotient (I − Ad_C)S_t/t = (I − Ad_A(t))S_t/t converges to −[H,K], which lies in the closed subspace h + h_C. So [H,K] is symmetric. It is also skew, so it is 0. Then K is diagonal and lies in h ∩ h_C = 0, which contradicts its unit norm.
- Openness has a clean global form. The augmented linear map (S, alpha, beta) -> ((Ad_A − Ad_C)S, (I − Ad_C)S − alpha − Q beta Q^-1) is injective exactly when (5.1) is injective and h ∩ h_C = 0. That is a maximal-minor condition in (A, Q), regular on T × SL_r.
- The distinct-a_I condition is nonempty because e_I − e_J is not a multiple of (1,...,1) when I ≠ J with |I| = |J|.

**Two-band tangent certificate (§6).** I recomputed every derivative.
- At regular semisimple A and C, stationary characteristic coefficients give delta A = [H_A, A] and delta C = [Z, C].
- The u0 variation is A^k[(V+Z)C^l B + C^l(Ad_B U − Z)B], which is (6.1). Formula (6.2) holds because A^k is diagonal. Vandermonde in k applies because the a_I are distinct and nonzero, for each j < r. Density of positive powers of C in T_C extends the identities to all N in T_C.
- At N = I, the trace gives W_ii = 0. Differentiating the 2×2 identity along K in h_C gives −B_ii B_jj (K_ij W_ji + K_ji W_ij) = 0, using P_ij(I) = 0 and the identically vanishing 1×1 terms. P1 then gives W = 0.
- Apply the lemma to M = NB, with triangle differences scaled by B_ii B_jj B_kk ≠ 0. Since h0 and B commute, [h0, NB] = [h0, N]B. By regularity, X − h0 lies in h_C after trace normalization.
- Removing conjugation by h0 gives (6.3) with S = Ad_B U, because the h_C part of Z − h0 commutes with C.
- The relation derivative is (Ad_A S − S) + (S − Ad_C S) = (Ad_A − Ad_C)S.
- The u1 derivative is T0 M + A^k B(S − T0)C^l − M S = [T0, M] + A^k B[R, C^l], which is (6.4). The lemma applied to BN gives R in h + h_C. This is exactly (5.1), so S = 0, and the whole tangent vector is an infinitesimal conjugation.
- Irreducibility holds: B has distinct entries and C has no zero entries.
- Submersion holds: the image contains Im(Ad_A − I) + Im(Ad_C − I), and its trace annihilator is h ∩ h_C = 0.
- Smoothness of the character variety at an irreducible smooth point of Hom, with tangent equal to the Hom tangent modulo conjugations, is classical (Luna slice or Goldman), not a new deduction.

**All genera and finite selection (§7).**
- The extra commutators have zero derivative at identity entries, so the extra variables are free. Conjugation acts trivially on them.
- After the core gauge, tr(U_kl delta A_i) and −tr(U_kl delta B_i) remain. The matrices U_kl with 1 <= k,l <= r span M_r: A^1..A^r span the diagonal matrices, row i of C^l is sum_j mu_j^l Q_ij row_j(Q^-1), and Vandermonde in mu with Q_ij ≠ 0 spans every row.
- The cotangent dimension is (2g−2)(r^2−1), so a finite subfamily F of curves spans.
- The combined Jacobian has rank 2g d − d, with d = r^2 − 1. This rank condition is a nonzero minor that is regular in (A, B, Q), so the set of (B, Q) for which it is not identically zero in A is a nonempty open set.
- Note: P1, P2 and (5.1) are used only to show that this minor is nonzero somewhere. They are not required at the final point.

**Arithmetic first, nonresonant complex A second (§8).**
- At Q = I, the map A -> A^k B C_mu^l -> T/W is finite and surjective. A Jacobian minor is nonzero at some point, so dominance holds on a nonempty open set of (B, Q) in the fixed eigenvalue class.
- Every band curve in F, including u0, u1 and the extra-handle curves, has monodromy A^k B C^l along the family.
- Dense arithmetic pairs (B(m), Q in SL_r(Z)) meet the finite intersection of nonempty opens. Then rho_0 is integral and satisfies the relation.
- Powers of the twist a -> ab give (B^n, B, C, I, ...). Since B generates T densely and the quotient map is continuous, the orbit closure Z contains the whole family rho_A, A in T.
- A complex A is then chosen outside countably many proper closed subsets (preimages under dominant spectral maps of Weyl images of character kernels and of the discriminant locus) and inside the finitely many opens. Baire on T applies.
- This order of choices is legitimate. No arithmetic nonresonance or Hilbert irreducibility is used.

**Spectral covers and dense nonresonance (§9).**
- On Z0' (Z0 intersected with the smooth irreducible locus where the gamma-monodromies are regular semisimple, which contains x), the eigenvalue-ordering cover is finite étale.
- A flat morphism sends generic points of components to generic points (going-down), so every component dominates the integral base Z0'. Finiteness makes each component surject.
- At x every ordering is independent, so each character relation cuts a proper closed subset of each component. Its finite image is proper in Z0'.
- Proper Zariski-closed subsets of an irreducible variety are nowhere dense in the classical topology, so Baire gives density in Z0 near x.

**Torus saturation and ideal invariance at singular points.**
- At such a point y, a fixed positive power of the twist about gamma preserves Z0. It acts as the cut-surface twist by rho_y(gamma)^N, and these powers are dense in the connected centralizer torus. The regular map from the torus to X sends a dense subset into the closed set Z0, so the whole torus twist orbit lies in Z0.
- Goldman Theorems 4.5 and 4.7 (the nonseparating HNN formula 4.6) identify the Hamiltonian flow of f_alpha with the twist by exp(tF(phi(alpha))), where F takes values in the centralizer. Lemma 1.11 and §3.16 handle real and imaginary parts for SL(n,C) with the form 2 Re tr. So each Hamiltonian field is tangent to the twist orbit at y.
- Hence X_f h vanishes on a dense subset of Z0 ∩ U for every local generator h of the coherent radical ideal, so X_f h_j = sum_k a_jk h_k. Uniqueness for the linear ODE along integral curves, in real time along each complex direction, shows that the flow preserves Z0, including through singular points of Z0. No Zariski tangent space of the singular closure is used as a neighbourhood.

**Open set and irreducibility.**
- The Hamiltonian vectors span T_x X because the form is nondegenerate.
- The composite of flows from x has surjective derivative and stays in Z0, so the holomorphic submersion (inverse function) theorem puts an open subset of X inside Z0.
- X_g,r is irreducible, so Z0 = Z = X_g,r.

**Ambient irreducibility contract (D1).**
- The candidate correctly uses the determinant-one fiber S_C(1) = Hom(pi_1 Sigma_g, SL_r), not the GL_r statement of prop:surface-irreducibility. In surfaces.tex, lines 125–248 establish the SL_n fiber over finite fields, via the Frobenius formula, character-degree bounds and Lang–Weil. They then pass to characteristic zero by spreading out, with dimension (2g−1)(n^2−1) for n >= 2, g >= 2 and c^n = 1. Lines 249–258 pass to GL_r.
- GL_r irreducibility alone would not imply this. S × G_m^(2g) maps onto R with finite fibers, and that only makes mu_n^(2g) transitive on the components of S.
- The candidate does not make that inference.

## Dependency classes the PASS rests on

- **D1.** Determinant-one irreducibility. This is an assertion established inside the proof of a pinned source proposition, not the proposition's own statement. I read its argument and found no gap at review depth, taking Lang–Weil and the Frobenius formula as standard. I treat it as stipulated upstream content.
- **D2.** Rank two is by citation of Coccia–Litt, arXiv 2507.00167v1. I read the §2 group definition, Proposition 3.1.10, and the statement and full proof case list of Proposition 5.0.1, including the n = 0, g >= 2 case (separating curve, 4.2.6/4.2.8, gluing), and Theorem 5.0.2. Their representation is an actual SL_2(O_L) homomorphism with a dense Gamma_(g,0) orbit in the Q̄ character variety, which is also Zariski dense over C. Their §4 constructions and Lemma 3.1.8 were not re-proved. This is outside the pinned-source stipulation and is accepted as the frozen scope's declared citation.
- **D3.** Classical inputs, not new deductions: the Luna-slice smoothness and H^1 tangent space at irreducible smooth points, the nondegeneracy of Goldman's form, Goldman's twist-flow theorems, coherence of analytic ideal sheaves, Dehn–Nielsen–Baer/Zieschang realization of boundary-fixing automorphisms, generic smoothness in characteristic 0, and Baire.

## Required objections

None.

## Editorial corrections and optional improvements (non-blocking)

- **E1 (correction, §4 P1).** For r >= 4 the witness H must specify its remaining off-diagonal entries. "Determinant one, independently of the diagonal entries" holds when sum_(k>3) H_1k H_k2 = sum_(k>3) H_2k H_k1, for example when all other off-diagonal entries are zero. With that choice H is regular for generic diagonal.
- **E2 (§8).** Say explicitly that the discriminant locus is avoided for each band spectral map, so that the selected monodromies are regular semisimple. It is implicit in "on the regular semisimple spectral locus".
- **E3 (§§1, 9).** Spell out the passage from Goldman's real orthogonal-structure flows (f = Re h, Im h; Lemma 1.11) to holomorphic Hamiltonian fields. Alternatively, run the final submersion with the real Hamiltonians of Re h and Im h. Also state that a neighbourhood of x lies in Goldman's smooth locus D/G (irreducible smooth points).
- **E4 (§3).** Cite the realization of relator-fixing automorphisms by boundary-fixing homeomorphisms (Zieschang/Dehn–Nielsen), or identify b -> ba^m and d -> dc^n as twist powers about a and c.
- **E5 (§5).** Replace "after choosing a local basis" with the augmented-map formulation above, which is global on T × SL_r.
- **E6.** Section 6 calls the extra-handle trace extraction "subtracting the trace differential of the core curve". After the core gauge the core variation is already zero, so nothing needs to be subtracted.

## Reviewer finite diagnostics (not proof)

reviewer-diagnostic.py was written independently, without reusing author code. Of the author's diagnostics I saw only the first 1500 bytes of simple-band-diagnostic.py. It uses exact arithmetic modulo primes p at which X^r − 3X^(r−1) − 1 splits, with C eigenvalues equal to reductions of eta·alpha_i, B = B(m), and random Q in SL_r(F_p).
- For (r,g,p) = (3,2,1069), (3,2,1097), (3,3,1069), (4,2,1481), (4,3,1481) and (5,2,1009), the relation rank is r^2−1, and the kernel of the combined Jacobian (a, c, u0, u1, extra curves with k,l <= r) equals r^2−1, the conjugation dimension.
- The residual system (5.1) has zero kernel. P1 holds and a P2 element is found.
- Dropping u0 or u1 in genus 2 enlarges the kernel. Dropping the extra-handle curves in genus 3 leaves 2(r^2−1) undetected directions.
- Free-group checks confirm the relator-fixing maps and the identities u0 = image of bd and u1 = image of abcd for k,l <= 4. Ribbon checks confirm one boundary and noncrossing based words for genera 2–5.
- Negative controls behave as expected: Q = I gives a nonzero residual kernel and kernel 20 > 8, and a crossing chord pattern is detected.

These are reductions at finitely many ranks. They are not a characteristic-zero specialization theorem, an all-rank argument, or an orbit computation.

## Exact read and search limits

- Read in full: AGENTS.md, sources/upstream.json, the acceptance section and opening of frontier/NEW-TEN-2026-10-14.md (lines 1–60 plus grep; no T027O entry exists there), candidate027o.md, scope027o.md, source-and-credit.md, verify.py, README.md, checkpoint.md, formal-interfaces.md, reading-limits.md (with 17 lines skipped in display), control-tests.py, controls.json (head), and source surfaces.tex (all 265 lines).
- Read in part: orbit-work.md (first about 6000 bytes, historical), simple-band-diagnostic.py (first 1500 bytes), primary-receipts.json.
- Coccia–Litt text: lines 380–470, 680–760 (Proposition 3.1.10 statement and opening of its proof), 1300–1430, and grep hits.
- Goldman text: lines 60–125, 380–475 (§1 through Lemma 1.11 with its proof), 1040–1075 (§3.16), 1160–1250 (Definition 4.2; Theorems 4.3, 4.5 and 4.7 statements; §4.6). The full proofs of 4.5 and 4.7 were not read, nor were the rendered page PNGs.
- Not read: source dynamics.tex, introduction.tex, model.tex and the other source sections (the candidate imports no contract from them), Pickrell–Xia, Mantelos, Loewy, the author's tangent and ribbon scripts and their JSON, context-receipts.json, source027-receipts.json and source-family-inventory.json beyond what verify.py and my canonical comparison check, and provenance/.
- No web retrieval was performed and no new third-party body was fetched, so this directory has no private/ folder.
- The parallel independent draft and the /var/tmp directories of other lanes were not read.
- The preprint tree was searched by directory title only. That search found no other character-variety title, and companion relevance was not assessed (contribution scope).

## Unchanged-scope disposition

The frozen target is unchanged: all g >= 2 and r >= 2, one actual integral orbit, density in the entire complex SL_r character variety, under orientation-preserving mapping classes. The verdict is not obtained by restricting genus or rank, by a union of orbits, or by any generic-input hypothesis. Rank two is Coccia–Litt's and is credited, not claimed. No punctured or peripheral claim is reviewed or passed.

No staging, commit, shared index or count edit, upload, publication, or nested agent was used. The author packet was not modified.
