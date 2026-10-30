# T197H independent adversarial proof review, round 1

Verdict: **PASS_FULL_T197H**

Required objections: **0**. Optional (exposition) objections: **6** (O1–O6 below). None changes a constant, a quantifier or the scope.

This is an independent proof gate on the frozen author packet `fresh-structural-discovery-r49/` (MANIFEST.json SHA-256 `819bc0a77c9ae52ca8a1b2193f64fc2f84754c17b6d5e0750c0be0ae351fd8b2`, verify.py `3483b937…6a`, candidate.md `5f02ca96…c75c9`, original-scope.txt `55cc403d…2b0191`, checkpoint.md `b06cb4ba…e176`). Pinned theorems at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true; only the new deductions were validated. No contribution or substantiality verdict is given. The campaign count and shared metadata are not touched. The parent alone adopts.

## Scope checked

The full unchanged scope in original-scope.txt: there exist a finitely presented torsion-free word-hyperbolic group G, a finite two-dimensional K(G,1), and a,b,c in F₂[G] with ab=1, ac=0, c≠0; hence ba≠1 and G is not sofic. Existential only; no executed presentation, complexity bound or other characteristic. The candidate proves exactly this statement. It is not weakened to a conditional, zero-divisor-only or nonhyperbolic statement.

## Source contracts actually used (read in the pinned bodies)

- source197 `thm:bounded-patterns` (patterns.tex lines 27–48): ε>0 depends only on alphabet and turn weights; for every K₀≥1, C≥1, I≥0 the P_L-probability of a system with ≤K₀ positive closed cyclically immersed paths (plus optionally one rooted interval), L≤H≤CL, ≤I comparisons with distinct underlying edges, b₀≤εH tends to 0. Comparisons are disjoint equal-length position intervals whose words agree or are t₁…t_h versus t̄_h…t̄₁; positions are disjoint.
- source197 `prop:diameter`, `lem:closure` (fixed D₀; segment retained, ≤D₀L appended, cyclically immersed), `lem:paired-intervals`, `lem:separator` (C_sep), `thm:no-arrangements`, `prop:cone-criterion` (asphericity, root protection, finite ≤2-dim complex, torsion-free), `prop:types` (parities for all x,x′∈A, y∈B and every outcome), `prop:parity` (loopless immersed graphs + parities + root protection ⇒ ab=1, ac=0, c≠0), assembly.tex.
- Gruber 1210.0178v2 lines 612–618: finitely presented with a linear isoperimetric inequality ⇔ Gromov hyperbolic (citing Alonso et al.).
- Elek–Szabó math/0305440v2 line 344, Corollary 4.7: D(G) stably finite for sofic G and division ring D.

## Independent re-derivation

### 1. Finite presentation and ordinary area (candidate §2)

Presentation P: rose letters; one relator r_e = label(t_u e t_v⁻¹) per non-tree edge of a spanning tree T_Λ of each component Λ. Since F has one vertex, van Kampen for attaching the contractible cone along Λ→F kills the normal closure of label(π₁(Λ,o_Λ)), which the r_e normally generate. So P is a finite presentation of G=π₁(X). (source197 topology.tex uses exactly this relative replacement.)

Area of a lifted loop: for a closed path p=e₁…e_h in Λ with vertices v₀=z,…,v_h=z, the identity t_z p t_z⁻¹ ≃ ∏ᵢ t_{v_{i-1}} e_i t_{v_i}⁻¹ holds in the free groupoid; each factor is a tree backtrack (freely trivial label) or r_e^{±1}. Applying labels, label(p) is freely a conjugate of a product of at most h relator letters. Repeated edges, start vertex and orientation are all covered. Confirmed.

(2.1): the complement of the inner disks is a disk with holes mapping to the rose, so in the free group w equals a product of conjugates of the inner boundary labels (with induced orientation). Hence Area_P(w) ≤ Σ Area(inner) ≤ H. Confirmed, with no minimality used.

Existence for a non-lifting boundary: w null in G gives w = ∏ g_i r_i^{±1} g_i⁻¹ in F; the standard disk-with-holes realization maps the complement into F and each hole is capped by coning its closed lifted basis loop into K_Λ. This is a cone picture in the source's sense, except that no Γ-lift of the outer boundary is specified. The source's Lemma `lem:cone-pictures` (disk case) assumes a Γ-path boundary, so the candidate rightly does not cite it for this; the van Kampen route suffices. See optional O1.

### 2. Fixed-boundary minimization (candidate §3)

The minimization is over all cone pictures filling the fixed parametrized word w, with no homotopy-class constraint. That is what makes component-discarding legitimate. H is a nonnegative integer, so a minimum exists. In a minimizer:

- Inner boundaries are positive and cyclically immersed: a non-tight inner path can be cyclically tightened inside its cone (collar homotopy, contractible cone), strictly lowering H. Constant disks are removed at no cost. Labels of cyclically immersed paths in an immersed graph are cyclically reduced words (algebra.tex).
- At least one inner disk exists, because a nonempty cyclically reduced w is nontrivial in F. By girth, H ≥ L.
- Two inner occurrences joined by an arc never traverse the same undirected edge e. Inverse letters on one edge mean opposite traversals. The thin band around the arc lifts into the interior of e.
  - Different inner disks: both lie on the component containing e, so the union disk+band+disk factors through one cone. The boundary (eP, e⁻¹Q) becomes PQ, so H drops by 2. The outer word is untouched.
  - Same inner disk: the band lies in the interior of Σ, so the formal exterior D∞ lies in exactly one complementary disk Q_i of the annulus N. Retain Q_i, cap its new boundary through K_Λ (a closed path in Λ by the source's word formula eP e⁻¹Q ↦ (P,Q)), and delete D∞. The result is a disk with the same boundary word w. The retained cap has length ≤ |P|+|Q| = h−2. Discarded disks only reduce H. Thus H drops by at least 2.
  - No sphere essentiality, homology identity or asphericity is needed, because any filling of w is admissible.
- Inner–outer and outer–outer arcs receive no edge condition, and none is needed later.

The minimal picture is simultaneously tight in all three senses (tight, no constant disks, no same-edge inner arcs), since each failure separately lowers H. Confirmed.

General position: the complement maps to F with ∂Σ reading w letter by letter. Preimages of edge midpoints are properly embedded arcs and circles, every occurrence carries exactly one arc end, and arcs pair inverse letters. This is the source's argument verbatim, and it does not use an outer lift. Confirmed.

### 3. Interval lemma with a formal exterior (candidate §4)

I re-derived the planar count for N boundaries that are cyclically reduced words, with no lifts assumed.

- χ(R)=N−E, Σχ(Q)=2−N+E, Σℓ_Q=2E ⇒ Σ(ℓ_Q−2χ(Q)) = 2N−4. This holds for disconnected R, loops (both ends on one disk) and parallel bands. ℓ_Q ≥ 1 because every boundary has positive length and every occurrence is paired.
- Monogon: its gap joins the two ends of one arc, which are cyclically consecutive occurrences with inverse letters. This contradicts cyclic reduction of whichever boundary it is on, including the outer w, so M=0. A length-1 boundary cannot carry both ends of one arc, so it produces no monogon either. It only produces same-band digon or positive-contribution corners.
- Same-band digons: each corner is the sole gap of a degree-one disk, giving ≤N such digons and ≤2N gaps.
- Other regions: disks with ℓ≥3 satisfy ℓ≤3(ℓ−2). Nondisk planar regions satisfy χ≤0, so ℓ≤ℓ−2χ. Distinct-band digons are good and contribute 0. Nongood gaps ≤ 2N + 3(2N−4) ≤ 8N.
- Cuts = nongood ∪ marks ∪ opposite(marks ∩ good), with marks = indexing gaps (≤N) plus piece-division gaps (≤N*). J ≤ 8N+2(N+N*) ≤ 12N*, using N≤N*.
- Runs between cuts map to whole runs in reverse order. If the gap after a run's endpoint partner were uncut and good, its opposite (the gap before that endpoint) would be good and uncut, which contradicts cut-set stability. A run cannot be self-paired: in odd length the middle is a fixed point, and in even length the middle letters would be adjacent inverse letters. So there are ≤6N* interval pairs, each inside one piece, and each is of reverse-inverse type as the source theorem requires.

Only cyclic reduction of words is used. Distinct underlying edges matter only for retained inner–inner pairs. Confirmed.

### 4. Boundary-defect estimate (candidate §5)

Constants (5.1): with ε=min(ε₀,1), I get 3D/U ≤ ε/64 from U≥192D/ε; ηU ≤ min(1/32, ε/64); C_sep/√K ≤ η. C and I are fixed before n. The order is ε₀ (alphabet/turn weights), d, D, then U, η, K, C, I, then n. Only one triple (K,C,I) is used. Confirmed.

Outcome selection: girth (conditioning), the diameter bound, no reduced spherical arrangement, and no forbidden system for this one triple. Each fails with P_L-probability o(1). A finite intersection is nonempty for large admissible m, and parities hold for every outcome. One outcome is fixed, and everything afterward is deterministic for every word. There is no union bound over words or diagrams. Confirmed.

Contradiction from H ≥ 32B/ε:

- Splitting: for h>UL, r=⌈h/(UL)⌉ ≥ 2 and h/r > UL/2. So pieces are ≥⌊UL/2⌋ ≥ UL/3 when UL≥6 and ≤UL, with integer lengths. The piece count is ≤3h/(UL), so H_add ≤ 3DH/U ≤ εH/64. N′L ≤ H follows from girth (intact) and UL/3≥L (cut). Closed pieces are cyclically immersed and keep their segment.
- The interval lemma is applied to N′ inner pieces plus one intact exterior piece: N*=N′+1, giving ≤6(N′+1) pairs. Deleting the exterior removes whole pairs (each interval lies in one piece). Outer–outer pairs vanish without loss. Inner positions unpaired by this step are ≤B, one per outer occurrence. No other inner position loses its partner.
- Planarity: replace each inner disk vertex by sector vertices for its pieces, then delete the exterior vertex. The retained-arc multigraph on N′ pieces is planar (loops and parallels are allowed). The separator deletes ≤ηN′ pieces, M ≤ ηN′UL ≤ ηUH ≤ εH/64 ≤ H/32. Retained pairs need both pieces alive, so they are whole and lie in one cluster.
- Budgets: ΣH_Z ≥ 31H/32. Σb_Z ≤ B+M+H_add ≤ εH/32+εH/64+εH/64 = εH/16. ΣI_Z ≤ 6(N′+1) ≤ 12H/L (since H≥L). H_Z ≤ K(U+D)L = CL. Unpaired positions are exactly closures, ex-outer partners and separator losses, because every original inner position was paired.
- Discards cost ≤H/16 each, leaving ≥27H/32 > 0. A surviving cluster has ≥1 positive cyclically immersed closed path, so H_Z ≥ L. It has ≤K paths, ≤I comparisons (192H_Z/L ≤ 192C ≤ I), b_Z ≤ εH_Z ≤ ε₀H_Z, and distinct edges on every retained pair. No rooted interval is used. This is a forbidden system for (K,C,I), a contradiction.

Hence H < 32B/ε for the minimizer, and Area_P(w) ≤ (32/ε)|w| for every nonempty cyclically reduced null word. Confirmed. Rational arithmetic was re-checked by hand: 31/32 − 1/16 − 1/16 = 27/32.

### 5. Conclusions (candidate §6)

- Arbitrary null w is freely conjugate to cyclically reduced v with |v|≤|w|, and the area is unchanged. So P has a linear isoperimetric inequality, and G is hyperbolic with respect to the finite rose generating set (Gruber lines 612–618 / [Al91]). Confirmed.
- The same outcome satisfies `prop:cone-criterion`: X is a finite aspherical complex of dimension ≤2 and G is torsion-free. It is also finitely presented. X has 2-cells (components have cycles), so it is a finite 2-dimensional K(G,1). G is not free, since free groups are sofic and the next item excludes soficity. Confirmed.
- With L≥3, the graphs are loopless. `prop:types` parities and root protection then give a,b,c (finite sums) with ab=1, ac=0, c≠0 via `prop:parity`. Hyperbolicity is an extra property of the same outcome and does not interfere. ba=1 would give c=(ba)c=b(ac)=0. G nonsofic follows by Elek–Szabó Cor. 4.7 (F₂ is a division ring). Confirmed.

## Checklist from the dispatch

All items pass: relative cone picture for a nonlifting boundary (§1); fixed-inner-perimeter minimization (§2); self-band surgery keeping the outside without sphere essentiality (§2); simultaneous tightening (§2); interval-gap count for disconnected arc graphs, loops, parallel bands, monogons/digons and a formal outside without a lift (§3); integer piece lengths and closure (§4); whole intervals when deleting the outer and separator vertices (§4); outer–outer arcs (§3–4); planarity after splitting (§4); no uncharged deficits (§4); ε before K,C,I and one outcome for all words (§4); ordinary basis-relator area including conjugation (§1, §5); compatibility with the exact source197 algebra, asphericity and finite dimension (§5); standard hyperbolicity and soficity implications (§5).

## Optional objections (exposition only)

- **O1** §2: write out the van Kampen realization of a cone picture for a non-lifting null word, as above. State explicitly that `lem:cone-pictures` (disk case) is not used, because it assumes a Γ-path boundary.
- **O2** §3: state that the minimization class has no homotopy-class constraint, and that this, rather than essentiality, justifies discarding the non-exterior component. Also state that the band is interior, so D∞ lies in exactly one complementary disk, and that the cap boundary is a closed Λ-path by eP e⁻¹Q ↦ (P,Q).
- **O3** §4: state N ≤ N* when concluding J ≤ 12N*. Note that M=0 gives 8N−12. Note that a length-1 boundary cannot create a monogon.
- **O4** §5: state that `thm:bounded-patterns` is invoked with ε₀ and that using ε=min(ε₀,1) only tightens b_Z. Record that every original inner occurrence was paired, so the three listed sources exhaust the unpaired positions.
- **O5** §6: the hyperbolicity criterion is recalled in Gruber (citing Alonso et al. 1991). The original was not read by the author or by me. It is standard, and this is not a gap.
- **O6** §6: note that X has 2-cells, so "dimension at most two" in the source becomes exactly two in the scope statement.

## Validation performed (identity only, not mathematics)

See `checks/controls-results.json`, produced by `checks/reviewer_controls.py` on disposable copies under /var/tmp, which were removed afterwards:

- The author verifier accepts the original packet with the external anchor and rejects a wrong anchor. It also accepts a positive copy, rejects a one-byte change to candidate.md, and rejects a fully resealed counterfeit source body under the external anchor.
- I independently compared all 29 private source bodies, by Git blob SHA-1 and size, against sources/preprints-tree.json. That file's SHA-256 is `eeecc1da…dc5e09b`, it has 13223 entries and truncated=false, and it was checked separately rather than through the packet's copied selection. All 29 match. The counterfeit body is caught here.
- Recorded author-verifier limits, reproduced: (a) a path through an ancestor symlink is accepted; (b) a counterfeit source with resealed receipts, selection and manifest is accepted under its own self-computed anchor. Only the external anchor or the canonical-tree comparison rejects it. No stronger property is claimed for the author verifier. My own check found no symlinks among the ancestors of the actual author packet path.
- All 13 supplied author controls were replayed on a copy and pass. The author finite ribbon/budget diagnostic was replayed and matches checks/finite-results.json exactly. It is finite and not a proof.
- This directory's own verify.py was exercised on disposable copies of the pre-seal tree, with temporary sealing in each copy. Results are in `checks/verifier-controls-preseal.json`: the positive copy is accepted, and the following are rejected: wrong anchor, a changed payload, a missing payload, an extra file, an extra directory, a root symlink, an ancestor symlink, a payload symlink, a hardlink, a FIFO, and a self-resealed status flip under the external anchor. Final positive and wrong-anchor checks on the sealed directory are reported to the parent separately.
- All 79 descendant nodes of the author packet (58 regular files with link count 1, and 21 subdirectories; 22 directories counting the root) were unchanged in content and link count before and after. A separate sha256sum snapshot of all 58 files also re-verified unchanged.
