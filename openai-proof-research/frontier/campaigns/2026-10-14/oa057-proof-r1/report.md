# OA057 independent full-proof review, round 1

Reviewer report for Myeongjin Kang (no affiliation). 2026-10-17. Original prose is CC BY 4.0 and original code is MIT. Third-party source bodies were read in the author's private snapshots. They are not copied here and keep their own rights.

## Verdict

**PASS_FULL_OA057.** The frozen candidate proves every quantifier of the frozen OA057 scope, given only the stipulated manifold theorem. Required objections: **none**. The nonblocking items in Section 5 are editorial; none of them is needed to repair the proof.

This is a proof verdict only. **Contribution/eligibility is a separate decision and is not made here.** No count, acceptance, manuscript, formal-support or release gate is granted or implied. The campaign stands where it was: target 20, 10 accepted. The checksums below authenticate bytes; they certify no mathematics. The author's finite diagnostics are reviewed in Section 6 as diagnostics only.

## 1. Exact inputs reviewed

All paths are relative to `frontier/campaigns/2026-10-14/`. Before reading, I recomputed the frozen dispatch anchors and they match:

| file | SHA256 |
|---|---|
| fresh-arithmetic-discovery-r12/inventory.json | 30dab2f1f474a9644069b58eeead506968d8a495c3082c853d4d0988adc41451 |
| fresh-arithmetic-discovery-r12/candidate.md | ac2aa7a43e1812c0e18053264512815f37b22ec5b15af0c7663cd93e0ca32954 |
| fresh-arithmetic-discovery-r12/scope.json | 5b7d08ee2344828c1727ac8956f28b9e69f06ba2eafcc5f35fc69d6ec14a76e0 |
| fresh-arithmetic-discovery-r12/reading-and-comparison.md | 975932e7a63be1cf998ed16a62449284cfa21d4cb4838c68de81168760296677 |
| fresh-arithmetic-discovery-r12/verify_inventory.py | 81580cc82e9af0cac7ab6256ebd966bd11ec6dbdd6dc121a21f7e77e80ee0021 |

- **Author verifier.** I read `verify_inventory.py` before running it. With the frozen anchor it exited with rc=0 (52 files, 29 directories). With an all-zero wrong anchor it exited with rc=1 ("external anchor mismatch"). Our own verifier checks that these five files are still unchanged.
- **Source snapshots.** For all 17 author source snapshots I recomputed the Git blob IDs myself and compared them with the complete `sources/preprints-tree.json` (truncated=false, 13223 entries; the truncated `tree.json` was not used). All 17 match the tree and the receipts, at pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
- **Scope chronology.** scope.json is stamped 2026-10-17T13:13:56Z, before the final proof. Its quantifiers are the dispatch's quantifiers. The candidate's Theorem OA057 states exactly those quantifiers and adds none.

## 2. What I actually read

- **Author packet, read in full:** candidate.md, scope.json, reading-and-comparison.md, checkpoint.md, affine_checks.py, affine-checks.json and verify_inventory.py.
- **Pinned manifold paper:** introduction.tex lines 1–51, which contain the definition of specialness (no line bundle L with a nonzero map L→Ω^p and κ(L)=p, for 1≤p≤n) and `thm:abelianity` (the entire π_1 of every connected special compact Kähler manifold, in any dimension, is virtually abelian). I also read the parts of preliminaries.tex covering `thm:specialness-inputs` and the remark that line-bundle and saturated definitions agree. I did not audit its proof, as the dispatch stipulates.
- **Fourfold companion, read in full:** introduction.tex, transfer.tex (Prop. transfer), branched.tex (Lemmas branched-cover, branched-action; Prop. branched-model) and differentials.tex (Lemmas ratios, saturation, rational-descent; Remark conventions).
- **Fourfold companion, partial:** inertia-foundations.tex lines 1–190 (Lemma in:auxiliary, Lemma in:root-bound, the SNC rounding rule (in:rounding) with its averaging descent, and Prop. in:finite-stability). I only scanned theorem labels in inertia-minimality, inertia-inputs, inertia-descent and quadrics.
- **Not read:** the third-party primary PDFs (Campana, Campana–Claudon, Belmans–Demleitner–Núñez, Kresch–Vistoli). The proof verdict does not rely on them. I use only the classical interfaces listed in Section 4.
- **Campaign context:** the four mandated briefs. I read arithmetic-brief.txt, fresh-r17-brief.txt (head) and next-discovery-brief.txt; I keyword-searched the 117 KB fresh-r15 brief for review constraints but did not read it in full.
- **History check (bounded).** I grepped NEW-TEN, TEN-FINDINGS, TWENTY-FINDINGS, frontier/README, frontier/iterations, frontier/campaigns/*.md and proposals for abelianity, root orbifold, OA057 and half-weight.
  - The only non-catalogue hits were i98 (a source-corollary screen of family057, whose developed target was relative K3) and cross_family.md line 106 (a one-line family057 screen).
  - Neither develops a root-orbifold chain. This is a bounded keyword screen, not an exhaustive eligibility determination. Eligibility belongs to the contribution gate.

## 3. Scope coverage, quantifier by quantifier

| Quantifier | Where paid | Review |
|---|---|---|
| n=0 | §1 | X is a point and s=0, so G is trivial (or the stipulated theorem applies directly). Paid. |
| s=0, any n | §1 | R is X, G is π_1(X), and the stipulated theorem applies verbatim. Paid. |
| n≥1, any finite SNC collection, distinct smooth irreducible D_i | §§3–7 | No disjointness is used. Intersections are handled in the local normalization (§3), the stabilizer step (§4), Hartogs (§6) and meridian products (§7). Paid. |
| arbitrary m_i≥2: mixed, composite, non-prime-power | §§2–4 | M=lcm and d_i=M/m_i. The boundary coordinate d_i·a_i is nonzero in Z/M exactly when a_i≠0 in Z/m_i, and translation by a nonzero multiple of an exact-M point is nonzero. Paid. |
| differential-line specialness of R, with equivariant plurisections | §6 | Matches scope.json and the companion's Def. special. Paid. |
| conclusion: the entire discrete G, virtually abelian, no index bound | §7 | The proof gives a surjection from π_1(Y) onto G, followed by the stipulated theorem. No finite or linear image is substituted. Paid. |
| no added hypotheses: residual finiteness, linearity, uniformization, Picard divisibility, positivity, dimension/order/count bounds | throughout | None is used anywhere. Divisibility holds only on Y, through descended roots. Paid. |

## 4. Independent verification of each operation

I re-derived every step myself rather than following the candidate's text. The classical interfaces used are:
- Kummer theory over C(X) (which contains μ_M) and Bertini for very ample systems;
- local analytic normalization;
- Cartan's description of finite holomorphic quotients and GAGA;
- Hironaka resolution that is an isomorphism over the regular locus;
- indeterminacy of meromorphic maps on normal spaces has codimension ≥2 (Remmert), or the direct argument in 4.7;
- closedness of holomorphic forms on compact Kähler manifolds, and the Ehresmann fibration theorem;
- normal generation of π_1 kernels by meridians.

**4.1 Affine action (§2).**
- R_0 and the map x↦R_0^{-1}x+C commute, because R_0C=C.
- Their M-th powers are the identity, since the iterate is R_0^{-M}x + MC = x.
- An element h acts on W_ab by x↦R_0^{h_a-h_b}x+h_bC. This is well defined because R_0^M=1 and MC=0.
- If h_a=h_b=t≠0, the action is translation by tC≠0, since c has exact order M. So h acts freely on that factor, and hence on F.
- Each e_a has a fixed point on F: 0 on the factors where it acts by R_0, x_k=kc on the factors where it acts by R_0^{-1}+C, and anything on the rest.
- The candidate correctly does not claim that every element with support ≥2 is free. The author's negative control (M=6, coefficients (1,2), x_k=2k) shows that claim would be false.

**4.2 Kummer cover and global independence (§3).**
- Write f_ij = s_{D_i}^{d_i} s_{B_ij}/φ_i^M for a rational section φ_i of H_i.
- Let P be a prime component of B_ij. For general members, P lies in no other B and no D. So ord_P of ∏f^{c} is c_ij mod M, and a relation modulo M-th powers forces every c_ij to be 0.
- This uses only one component per B_ij, so it holds on curves where B_ij is a disconnected set of points.
- The extension therefore has degree M^r with Galois group A. S is integral (the normalization of X in a field), finite and projective.
- Bertini: general members of the very ample system are nonempty (n≥1), smooth and transverse to all previous strata. Chosen sequentially, they make D+ΣB SNC. A smooth B_ij has pairwise disjoint components, so at most one component of each B_ij passes through a point.

**4.3 Local normalization at every SNC stratum (§3).** I checked the candidate's charts by counting sheets.
- Let i∈J, and let K_i be the set of labels of block i that are present (pass through x). The SNC bound |J|+|K|≤n gives |K_i|≤n−1, so at least two labels of block i are absent.
- Take an absent label j_0. Its equation (y/u)^M=z_i^{d_i} factors into d_i branches (y/u)^{m_i}=ξz_i with ξ^{d_i}=1. Each branch normalizes to w_i^{m_i}=z_i.
- For the other labels: absent labels give y=c·u·w_i with c^M fixed, which is M choices. Present labels give v=y/(uw_i) with v^M=t, again degree M.
- Block i therefore contributes degree d_i·m_i·M^{N−1}=M^N, and blocks with i∉J contribute M^N. The total is M^r, matching the generic degree. The points of the generic fibre are distinguished by their y-values.
- So the smooth polydisc charts (w_i, v_a, remaining coordinates) map finitely and birationally onto the components, and are the normalization. S is smooth.

**4.4 Full inertia (§3, (3.2)).**
- Write ζ for a fixed primitive M-th root of unity. An element h∈A preserves a component over x and fixes the point exactly when three conditions hold:
  - its coordinates on all absent labels of block i agree, so the ratios c are preserved;
  - that common value lies in d_iZ/M, so ξ is preserved because ζ^{m_i h}=1;
  - its coordinates on absent labels of blocks with i∉J vanish.
- Present coordinates are unrestricted, since v_a=0 at the point. Hence H_x=⊕_{i∈J}⟨τ_i⟩⊕⊕_{a∈K}⟨e_a⟩.
- Order check: per boundary block, m_i·M^{|K_i|} = M^N divided by the number of points d_i·M^{N−|K_i|−1}. This confirms that (3.2) is the *entire* inertia group.
- τ_i multiplies w_i by ζ^{d_i}, a primitive m_i-th root, and leaves the v_ij unchanged. Each e_a changes only v_a. Also π^*D_i=m_iR_i with R_i={w_i=0} reduced.

**4.5 Stabilizers and root lines (§4).**
- The stabilizer of (s,f)∈V is H_s∩Stab(f).
- Take an element of H_x with some a_i≠0. On both absent labels of block i its coordinate is d_ia_i≠0, so by 4.1 it moves every point of F. Hence every point stabilizer lies in ⊕⟨e_b : b∈K⟩, which fixes every w_i.
- On R_i the frame 1/w_i of O(R_i) is therefore stabilizer-invariant. Off R_i, the invariant nowhere-vanishing canonical section trivializes the line.
- So every point stabilizer acts trivially on every fibre of every O(R_i), at all points of V, including all SNC and auxiliary intersections.
- Descent: take an H-invariant neighbourhood whose translates are disjoint, and average a frame. Its value at the point is unchanged because the action there is trivial. The invariant transition functions descend by Cartan.
- This descends T_i, t_i and the equivariant identity O(R_i)^{m_i}=π^*O(D_i), which is the canonical equality of divisorial subsheaves and sends the canonical section to π^*s_{D_i}. GAGA then algebraizes everything on the projective quotient Z.

**4.6 Resolution, multiplicities, projectivity, fibres (§4).**
- Z=V/A is projective, normal and irreducible. Choose a resolution ρ:Y→Z that is an isomorphism over Z_reg.
- ρ^*t_i is a nonzero section of the line bundle ρ^*T_i with (ρ^*t_i)^{m_i}=g^*s_{D_i}. Hence g^*D_i=m_i·div(ρ^*t_i) on Y, *including every exceptional prime*, and Y lifts to the root stack R.
- Locally, take an m_i-th root of the unit relating frames. The lift is unique up to the chart group μ_{m_i}.
- Over U, S|_U is an étale A-torsor, so Z|_U is the bundle S|_U×^A F: smooth, with fibre F. The general fibre of g is therefore the connected abelian variety F.
- A connected general fibre over a normal base gives g_*O_Y=O_X by Stein factorization, so all fibres are connected. Only general-fibre connectedness is actually used.

**4.7 Divisorial submersions (§5).**
- **At D_i.** At a general point (J={i}, K=∅), every nonzero element of ⟨τ_i⟩ has N≥2 equal nonzero coordinates. The action is free, Z is smooth there and ρ is an isomorphism, and Z is locally S×F. The lift to the root chart is the projection to (w_i, other coordinates), which is a submersion. This was checked against the descended t_i, which pulls back to the canonical section w_i.
- **At a component P of B_a.** At a general point, H_x=⟨e_a⟩ and Z|_{U_x}≅(S_0×F)/⟨e_a⟩. For v∈F^{e_a}, the map s↦[s,v] is ⟨e_a⟩-invariant, so it descends to σ:U_x→Z with hσ=id. Off P, σ lands in Z_reg, where ρ is an isomorphism.
- Let Γ be the closure of the graph of ρ^{-1}σ over U_x∖P. It is an irreducible analytic component of U_x×_Z Y, proper and bimeromorphic over U_x.
- **Independent argument.**
  - The positive-dimensional fibres of Γ→U_x lie in a proper analytic subset of Γ, of dimension ≤n−1. So the locus T over which those fibres lie has dimension ≤n−2.
  - Over U_x∖T the map is finite and bimeromorphic onto a normal space. Its structure sheaf is finite and contained in the meromorphic functions, hence integral over O_{U_x}, hence equal to O_{U_x}. So the map is an isomorphism there.
  - This gives a holomorphic σ̃ on U_x∖T with gσ̃=id. g is therefore submersive at σ̃(u) for u∈P∖T.
- The candidate's remark that "the image of the smooth locus is open" is correct, because smooth implies flat implies open. In any case only the local section is used in §6.

**4.8 Specialness transfer (§6).**
- The Bogomolov closed-form lemma, the trivial filtration with graded pieces ∧^kN^*⊗Ω^{p−k}_F on F, the constancy of t^qs_0|_F, rational descent (a degree-one argument in characteristic 0) and p≤n all check, as in the companion's Lemmas ratios and rational-descent.
- The relation (6.2) gives holomorphic h_a over a smooth open on which g^*σ never vanishes, and these descend to b_a.
- f^*(b_aσ^q)=i^q(s_a) holds as meromorphic tensors (equal on a dense open), so it is holomorphic.
- Pole tests by divisor type:
  - for a chart divisor over D_i, use the D_i section from 4.7 (any μ_{m_i} ambiguity is harmless because the tensor is invariant);
  - for a component of B_a, use σ̃;
  - for every other prime, use a local section where g is smooth.
- A chart divisor at a deeper stratum is, near its general point, étale-equivalent to one of these. Hartogs on the smooth charts then gives holomorphy everywhere.
- Saturation: a primitive generator stays primitive in tensor powers. If a prime divided every κ_{i_1}⋯κ_{i_q}, it would divide every κ_i^q. So the b_aσ^q are global invariant sections of K^q, and κ(K)≥p.
- f^*K→Ω^p_Y is nonzero, sections pull back injectively, and the Bogomolov bound on Y gives κ(K)≤p. This contradicts specialness of R. Y's specialness matches the pinned definition, so the stipulated theorem applies.

**4.9 Full group surjection (§7).**
- g^{-1}(D) is the support of an effective Cartier divisor, hence a hypersurface (possibly not SNC). The kernel of π_1(Y°)→π_1(Y) is normally generated by meridians of its components.
- For a prime Q, take a transverse disk at a general point q, and SNC coordinates at x=g(q), which may lie on any stratum, of any codimension, possibly exceptional. The loop has class Σ a_iγ_i in π_1(U_x∖D)≅Z^J with a_i=ord_Q g^*D_i. This class is divisible by the m_i by 4.6.
- Each local meridian of D_i at x is conjugate in π_1(X°) to γ_i. This holds because D_i minus the other components is connected, as D_i is irreducible.
- So each filled meridian dies in G, and π_1(Y°)→G factors through π_1(Y).
- Surjectivity: π_1(g^{-1}U)→π_1(U) is onto, because the fibres are connected (Ehresmann). π_1(U)→π_1(X°) is onto by complement removal. Composing gives π_1(Y)↠G. No residual finiteness or linearity is used.
- Finally, the image of a finite-index abelian subgroup is finite-index abelian. The proof is complete.

## 5. Objections

**Required (blocking): none.**

**Nonblocking editorial items** (the proof is correct without them):

- **N1 (§5).** The "localize at the generic point, DVR, extend by properness" sentence is an algebraic argument applied to the analytic section σ. It is better to cite Remmert's codimension-≥2 indeterminacy for meromorphic maps from normal spaces, or to give the dimension-plus-normality argument of 4.7. Also, "with its reduced structure and normalization" should not read "equivalently": the normalization is unnecessary.
- **N2 (§3).** The stabilizer formula (3.2) is asserted from the charts. Adding the explicit condition (equal absent coordinates lying in d_iZ/M) and the order count of 4.4 would make "entire inertia" self-evidently complete.
- **N3 (§7).** State explicitly that local meridians of D_i at points of deeper strata are conjugate to γ_i because D_i minus the other components is connected.
- **N4 (§4).** Add that the identity O(R_i)^{m_i}=π^*O(D_i) is the canonical equality of divisorial subsheaves, hence equivariant. This is implicit in the text.
- **N5 (§8 item 6, §4).** A side remark, unused in the proof: Stein factorization over normal X makes every fibre of g connected, not only the general one.

**Observations forwarded to the separate contribution reviewer (not proof objections and not a contribution verdict):**
- The companion's Lemma in:auxiliary already obtains exceptional root divisibility for order-two disjoint divisors under an arbitrary equivariant resolution. It does this through regularity of the roots on the normalization, not through descent.
- The companion's averaging descent and the SNC rounding rule (in:rounding) are antecedents, as the candidate itself credits.
- The candidate's own §9 credits the transfer criterion, the double covers, the pairwise affine idea and the group endpoint.
- Whether the remaining construction (exact-M cyclic shifts, n+1 labels per boundary component, descent before resolution, lifting fixed-point sections through an arbitrary resolution) exceeds a technical extension is for that gate alone.

## 6. Finite diagnostics: scope and controls

affine_checks.py replaces E by the additive group Z/M with c=1 and checks the formulas of 4.1 on vectors in (Z/M)^{Z/M} for M=2..32. The group law is tested only against the three second elements (1,0), (0,1) and (1,1). The mixed-inertia loop covers 8 order tuples up to lcm 12 and n≤5, and adds the same auxiliary shift from {0,1,M−1} to every present label.

Both negative controls are genuine:
- the support-≥2 claim is false (M=6, coefficients (1,2));
- a non-exact torsion point fails (3·2≡0 mod 6).

These diagnostics cover finite instances of elementary formulas that are proved universally in candidate §2 and in 4.1 above. They do not touch Kummer normalization, descent, resolution, specialness or topology, and were not used for the verdict. Formal support is not claimed by the author or granted here.

## 7. Limits

- This is a human-style reading and derivation review, not a formalization.
- The upstream theorem is stipulated and not audited.
- I made no priority or novelty judgment.
- Third-party primary PDFs were not read by me (Section 2).
- The history screen is the bounded keyword search described in Section 2.

No staging, commits, shared-ledger edits, nested agents, browsing, uploads or publication were performed. Integrity sealing: `manifest.json` lists every other file in this directory with its size and SHA256. `verify.py` refuses to run without an externally supplied expected SHA256 of manifest.json, and checks that anchor before parsing anything. It then checks exact membership, rejects symlinks, and re-checks the five frozen author anchors. `run_controls.py` runs the positive control, wrong-anchor and malformed-anchor controls, plus tamper and extra-file controls on a temporary copy. The manifest hash itself is reported outside this directory.
