# T195D93 independent contribution review, round 1

Verdict, conditional on correctness: **TECHNICAL**.

This review judges contribution only. It assumes the author proof is correct and does not assess that. The separate proof review and its brief were not opened. No prior contribution verdict existed. This verdict is not an acceptance, count, eligibility or worldwide-priority statement. Campaign 18/20 and publicationSTOPPED are unchanged. The parent integrates.

## 1. Exact claim reviewed

Author root `frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r93/`. The frozen statement `packet/public/FROZEN.md` (SHA256 `ac626f4a…7fa87572`) says:

For every smooth integral projective complex surface X and every ample globally generated Cartier divisor H, put h=H² and Δ=K_X²−2c₂(X). Let T be the full section ring, n=T_{>0}, and (R,m) the n-adic completion of T_n. For every nonzero finite reflexive R-module M of rank r, H²_m(M) has finite length and

    length_R H²_m(M) ≥ r·max(0,(Δ−3h)/24).

The constant is exactly 1/24. There is no K-proportionality, grading, algebraizability, rank, HN-length, denominator, asymptotic or semistable restriction. Nothing about effectiveness, equality, lim-CM, nonconical rings or characteristic p is claimed. I assess exactly this statement. I do not substitute a weaker surrogate.

All six detached anchors match the files byte for byte. These are FINAL.json `362dfe44…`, outside REPORT.md `761a6e49…`, packet/MANIFEST.json `8464240a…`, FROZEN.md `ac626f4a…`, proof.md `b05e2ea2…` and CONTROLS.json `759b2467…`. See `public/reading.json`. These are artifact checks, not mathematical gates.

## 2. The strongest compatible reduction

The author route is proof.md §§1–5. I compared it with the strongest actual operations already available. The table below gives the reduction that decides the verdict.

| Step of T195D93 | Strongest existing operation, at its actual contract | What is left after crediting it |
|---|---|---|
| Finite model, completion, finite length, L=length Ext¹_A(E,A)=length H²_m(M) | Source195 §2 (`sec:cone`, `eq:completion`, `eq:conormal`); Chen v1 Lemmas 2.4–2.5; standard local duality and Auslander–Buchsbaum | Nothing |
| Fixed HN interval [b,b+1) with unchanged punctured bundle | Source `lem:balance`/`eq:transform`; Chen Prop. 3.3 (window [3/2,5/2)); r83 `slope-budget.md` for arbitrary offset b | Nothing. The offset is a parameter of the same termination proof. |
| Upper bound Φ(F) ≤ rh(1/4−Δ/(12h)) at arbitrary K | Source `lem:factor` and `eq:RR-variance` (RR, Bogomolov, Hodge-index square completion at arbitrary K); r83 mixture identity | Nothing. Φ(F)/N=Σw_i(v_i+m_i²−m_i) is r83's identity in linear form. |
| Lower bound Φ ≥ 0 for every lattice of a trivial bundle | Source `lem:lattice` `eq:layers`/`eq:Tor`: 2ch₂ ≥ Σ(2j+1)n_j and c₁=Σn_j give Φ=Σ2j·n_j ≥ 0 at once | Nothing. This is the free-atom cost 0 and the L=0 case (r83's Δ≤3h). |
| Local stable filtration of E⊕A^u by exactly L Koszul atoms plus trivial factors | Horrocks 1980, Astérisque 71–72 pp.197–198 (projective nest with multiplicity Σ h¹, built by dismantling a dualized resolution into Koszul complexes). The local form is the standard punctured-spectrum version of the same proof. proof.md §2 proves it in full by dual resolution, composition series, horseshoe and Schanuel. | Only a classical transfer, which the author writes out. |
| Cost −2 for every lattice of ρ*B, B=T(−1)=Ω¹(2) | Source `lem:lattice` with the reference changed from O^N to ρ*B. `eq:Tor` does not depend on the reference. The capacity bound n_j ≤ rank holds as before. In `eq:layers`, "a quotient of a globally generated bundle has c₁ ≥ 0" becomes "a quotient of a semistable bundle has slope ≥ μ". Stability of T_{P²} is textbook. The minimization is the same fill-the-earliest-slots step as r83's hinge. | A one-line change of reference inside a paid lemma |
| Saturation, exact restriction, cancelling the stabilizing free summands | Saturation of a generic filtration on an integral scheme; Cartier Tor vanishing for torsion-free quotients; Φ(O_D)=0 | Nothing beyond elementary algebra |
| Applying the bound to the SAME balanced lattice | Not needed as a separate step. Bound (9) holds for every torsion-free lattice of E, so it covers the balanced g_*ℰ automatically. | No compatibility issue remains |

### Exact identification with Chen's architecture

On P², Riemann–Roch gives χ(F(t)) = N(t+1)(t+2)/2 + c₁(t+3/2) + ch₂. At t=−2 this is

    Φ(F)/2 = χ(D,F(−2)) = χ(X,P(−2H)),

using F=f_*P and the projection formula. So T195D93's chain is

    −L ≤ χ(X,P(−2H)) ≤ rh(1/8−Δ/(24h)).

Now specialize to K≡4H. Then b=7/2, so the slopes of V:=P(−2H) lie in [3/2,5/2). That is exactly Chen's normalization (3.5). Noether's formula turns the right-hand side into −c(Y,H)·r. So T195D93 has precisely the shape of Chen's §6 chain:

    dim H¹(U) ≥ −χ(V) ≥ c(Y,H)·r.

This chain is printed as a "Proposed proof" and is credited at that status only. T195D93 changes two links:

1. **Upper link.** Chen's Prop. 4.1 uses ν·K=4ν·H. It is replaced by source `lem:factor` together with r83's alignment, which hold at arbitrary K. This is fully paid.
2. **Lower link.** Chen proves "deficiency ≥ −χ(V)" with fixed-source persistence (Prop. 5.1/Cor. 5.4) plus two-tail estimates (Lemma 4.2, Prop. 4.3). The tails need the window and s(ω_Y)=4. T195D93 replaces this with a bound that holds for every lattice and does not depend on K. It is proved on D=P² by stable devissage and the atom costs. I do not extrapolate Chen's tails to arbitrary K. The earlier project text I28 §3 records exactly that limitation for K=5H.

So the only step not literally paid is the lower link at arbitrary K: L ≥ −χ(D,ℒ|D(−2)) for every lattice ℒ of a reflexive A-module E.

## 3. Is that lower link an unpaid operation?

**The strongest case for SUBSTANTIAL:**

- The arbitrary-K deficiency bound was explicitly left unclaimed in project history. I28 §3 says Chen's tails "do not apply unchanged" at K=5H, and I31's handoff disclaims quantitative bounds.
- Chen, a specialist primary, reached only K≡4H, with a long qualified argument.
- Chen's route also fails if transposed naively to D. The P² tails would need HN control of F=f_*P on P², and finite pushforward does not preserve semistability. So a genuinely different lower-bound mechanism is required.
- The resulting inequality is clean, uniform and new in the bounded reading. No identical formula was found.

**Why I nevertheless judge it TECHNICAL:**

1. **The obstruction was specific to one route.** I28 recorded a gap in the cohomological persistence-plus-tails route. It did not record a failed attempt along source195's own lattice route. Source195 states that its method "replaces that triviality condition by a comparison of coherent extensions across the exceptional divisor". Moving from trivial reference lattices to Horrocks atoms is the direct extension of that method.

2. **The devissage is classical, and its multiplicity is the classical one.** Horrocks's 1980 nest on P^n has factors that are twisted exterior powers of T. Their number is Σ_r dim H^i(E(r)). On P² the only factors are twists of T, and the count is the total h¹. The local analogue counts L=length H¹(U,E), via the same "dualize a resolution and dismantle it into Koszul complexes" proof. The author's §2 gives that proof locally, so no unread book is a dependency. A secondary MathOverflow navigation answer (not used as a primary) states the local theorem in the same form and points to Evans–Griffith Ch. 5 Thm. 5.2, which I did not read.

3. **Each atom costs the same as its graded model.** For the pullback lattices, Φ/2=χ(O(−2))=0 and Φ/2=χ(B(−2))=χ(Ω¹)=−1. These are one-line graded computations: −χ(𝔉(−2)) ≤ h¹(𝔉(−2)) ≤ Σ_k h¹(𝔉(k)). Extending them to every lattice is exactly what source `lem:lattice` does. The only change is replacing global generation by semistability in one line, which the B-atom requires. The optimization is r83's hinge. Additivity makes any extension data between atoms irrelevant, and the stabilizing free summands cost Φ(O)=0.

4. **No compatibility remains in the integration.** The lower bound holds for every lattice, so the "same balanced lattice" requirement holds automatically. The lower bound lives on P², so it does not depend on K. The upper bound is r83/source verbatim. No new lattice is chosen after balancing, and no grading is assumed. Nothing about the interface needs a new idea once Φ is recognized as additive and its per-atom minima are computed. Recognizing Φ is itself immediate: it is r83's hinge functional (for m∈[0,1), v ≥ m(1−m) is equivalent to Φ ≥ 0) and Chen's −χ(V).

5. **The formula is the predictable common generalization.** At L=0 it gives r83's Δ≤3h. At K≡4H it gives Chen's 15h/8−χ(O_X). The constant 1/24 is forced by r83's threshold together with the −2 cost of the single P² atom type.

The brief warns that "classical stable-devissage/Cartier capacities" might already pay a full formula. That is what happens here. The arbitrary-K, all-rank theorem is stronger than anything printed in the primaries. But its one non-inherited step is a short, standard composition: the Horrocks local nest, a reference change in the paid capacity lemma, and additivity. This composition introduces no new geometric or homological operation. Chen's specialist route failed to reach this generality, and I28 did not claim it. Those facts are evidence about routes not taken, not a mathematical obstruction that this proof overcomes.

**Not REDISCOVERED.** No read primary states the full theorem. Chen v1 covers only K≡4H, and its printed status is a qualified "Main claim"/"Proposed proof". Anghel v1 Thm. 1.1/§2 is a graded aCM threshold (L=0). It neither grades arbitrary completed-local modules nor bounds deficiency. Source195 `thm:obstruction` is the qualitative 6h MCM obstruction. r83 is the qualitative 3h MCM threshold.

**Not UNRESOLVED.** The verdict does not depend on an unread primary. The decisive transfers (source `lem:lattice`, r83 hinge, Horrocks pp.197–198, Chen §§3–6) were read at the extents in §5. Horrocks 1964 PLMS and Evans–Griffith Ch. 5 were not read. Their only role would be to supply the local devissage, which the author proves directly and which I judge classical either way. If some unread primary already contained the lattice-uniform defect inequality itself, that would push toward REDISCOVERED, not toward SUBSTANTIAL.

## 4. Boundaries and residual uncertainty

- This verdict is conditional on correctness and makes no correctness judgment. I did not audit truth upstream. In particular, I did not check the B-atom sum, the saturation or the Euler identification as a proof gate. I did recompute the B-atom sum, the free-atom sum and the final constant as reading aids: 2a²−2+2Σ_{j<−a}(2a+1+2j)=−2, a²−a+2Σ(a+j)=0, and −2L ≤ rh(1/4−Δ/(12h)) ⇒ L ≥ r(Δ−3h)/24.
- The closest call is item 1 of §3: whether choosing the devissage route over the cohomological one is itself the contribution. I judge it is not, because source195's lattice method makes it the default route. A reviewer weighting the I28 record more heavily could disagree. I record this as the main residual uncertainty, not as an unresolved gate.
- Chen's main claim and proposed proof are not treated as established or as stipulated truth. Its §§3–6 operations are credited at their printed hypotheses only, with no two-tail extrapolation to arbitrary K.
- The frozen bytes and full scope are preserved. No surrogate or repair was introduced.
- The author's prefreeze feasibility (the full formula and mechanism before the freeze) and the late but prefreeze discovery of r83 are disclosed. I did not use timing as mathematical evidence.

## 5. Reading, provenance and limits

Read in full: the author's HANDOFF.md and REPORT.md, and packet/public FROZEN.md, freeze.json, proof.md, comparison.md, report.md and rights.md. reading-limits.md and reproduction.md came through a terminal display that truncated their middle sections. I also read other-screens.md only through that truncated display, and not as decisive. The verdict does not depend on any truncated passage. I read parent intake.json, task-status.json, the replay.json head and the opening of assessment.md. I did not open the parent proof-review-brief.txt, any proof review or my own brief file. The parent directory later showed new `proof-r1-*` files and modified intake/assessment files, written by the parent and not by me. I opened none of the new files and did not reread the modified ones. What I had seen earlier said only that review was pending and contained no proof-review outcome.

Primary and source bodies were read from the author packet's private copies. Their hashes are verified in `public/reading.json`.

- Source195 `paper.tex` at fd4aeeb: lines 100–209 (statement, `thm:obstruction`, comparisons, overview) and 455–630 (`lem:lattice`, `eq:layers`, `eq:Tor`, `lem:factor`, `eq:RR-variance`, `eq:mixture`, proof of the obstruction). §§2–3 were not reread by me. Their operations are credited through the author and r83 descriptions and the label index.
- Chen 2609.24142v1. This is the only arXiv version, confirmed on the abs page on 2026-10-19. I read the abstract, outline, Main claim 1.1 statement area, and lines 270–624: §3 Lemma 3.1 and Prop. 3.3; §4 Prop. 4.1, Lemma 4.2 and Prop. 4.3; §5 Prop. 5.1, Lemma 5.2 and Cor. 5.4; and the §6 proposed proof. §2 proofs and §7 were not read.
- Anghel 2609.15589v1: targeted search of the Theorem 1.1/§2 structure (Lemma 2.2 Horrocks, Lemma 2.4 majorization, Remark 2.5) through a line index, not a full reread.
- Horrocks, Astérisque 71–72 (1980): the OCR text of pp.197–198 in full, including both theorems and the dismantling proof. The rest of the volume was not read.
- r83 `slope-budget.md`: read in full from the live path. Its hash equals the author's history copy, `1c7f6c4f…`.
- I28 §3, lines 160–219 plus a grep. I31: section index, the Chen table row and the review handoff. Live hashes equal the author's copies.
- Bounded external search (navigation only). I ran WebSearch queries for local-cohomology/section-ring deficiency, Horrocks punctured-spectrum syzygy, and local Chern/Ext¹ on 3-folds. I read the MathOverflow 20593 answer in full (secondary, not retained). For Miyazaki arXiv 2403.17625v3 (retained privately), I read the first page and a heading/term index only; it covers projective Horrocks-type criteria and no Chern-lattice deficiency. For X. Chen arXiv 2607.01402 I read the abstract only; it concerns rank-two local c₃ and is adjacent, not a match. No primary stating the lattice-uniform defect inequality or the full theorem was found. That absence is not a priority clearance.
- Not read: Horrocks 1964 PLMS, Evans–Griffith *Syzygies*, BHM 2410.18372 and source `surface.tex`.

## 6. Artifacts in this directory

- `REVIEW.md` (this file) and `public/reading.json` are original prose and metadata.
- `private/primary/` holds third-party copies under their original rights. They are not public originals.
- `public/verify.py` is a read-only verifier. It checks the author's detached anchors, the hashes of the cited bodies, and this directory's own `MANIFEST.json` against a detached `FINAL.json` hash supplied on the command line.
- `public/seal.py` writes `MANIFEST.json` and `FINAL.json` and prints the detached FINAL hash.
- `public/run_controls.py` runs disposable-copy mutation controls under `scratch/`, removes the copies afterwards, and records `CONTROLS.json` outside the manifest.

None of this is a mathematical gate. No upload, contact, git operation, shared-index edit or nested agent occurred.
