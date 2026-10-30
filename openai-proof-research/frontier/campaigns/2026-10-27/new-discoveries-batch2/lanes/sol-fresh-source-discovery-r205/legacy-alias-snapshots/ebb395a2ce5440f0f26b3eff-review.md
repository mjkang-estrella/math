# CDF098 independent adversarial proof review — round 1

Author of record: Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT. Third-party sources stay private in the author packet and are referenced here only by path and hash.

**Verdict: PASS_FULL_CDF098.** This is a proof verdict only. It does not decide contribution, eligibility, substantiality, novelty or acceptance (those belong to `cdf098-contribution-r1`, which I did not read), and it changes no campaign count.

## Reviewed bytes and identity

Author packet `frontier/campaigns/2026-10-14/fresh-parent-discovery-r8/`:

- manifest.json SHA256 `f417cfd409e18a34c97f488fb10ebfa25f1b09b5fc4ff323c53c71cf71262c85`
- original-scope.md SHA256 `bb115b9c504b9e5d8e3f62d841bc16095049f23719a47eb13d18d253ed1741c5`
- candidate.md SHA256 `24c5d7055f19b48bac26451a87896845756865eeeba5d0502e1f7982ccb6f39a`

I ran `python3 -I verify.py --anchor f417cfd4…2c85`. It returned `IDENTITY_ONLY` with 21 payloads, 2 pinned text blobs and 4 primary PDFs. That matches the parent replay. I also checked the two source Git blob SHA-1s myself against the complete `sources/preprints-tree.json` (SHA256 `eeecc1da…e09b`, `truncated=false`), and both matched:

- `build/main.tex` → `4c45439184128f24b1bde5cbcf3dc56d8f95afe3`
- `README.md` → `352f8d135eda49616687a2b10acf3eccf6d1732f`

Identity is not proof. Every new deduction below was rederived independently.

## Exact target reviewed (unchanged)

There is a finite universal integer Λ such that the following holds for every infinite-dimensional real Banach space B. There is a Lipschitz map γ:[0,1]→B whose image Γ has two properties:

- In the ambient norm metric, Γ is Λ-doubling. Every Γ-ball of every radius r>0, with center in Γ, is covered by at most Λ Γ-balls of radius r/2 with centers in Γ.
- Γ admits no finite-distortion bi-Lipschitz embedding into any finite-dimensional real normed space.

The candidate does not narrow this target. It uses the ambient metric throughout and never uses the graph or path metric. Λ is fixed before B is given. Γ is fixed before the target dimension and distortion are given.

## Part 1 — Lemma 1, the only new operation (fully rederived)

**Setup.** X is finite, |X|≥2, diam X=1, and X is D-doubling with centers in X (D an integer ≥1). Put s_k=2^{-k}.

- N_0={x0}. This is a 1-net because diam X=1.
- For 1≤k≤m, N_k is a maximal set with pairwise distances >s_k. Maximality makes it an s_k-net.
- Since |X|≥2 and diam=1, the minimum separation is ≤1. So s_m<minsep forces m≥1, and every pair in X is >s_m apart, which gives N_m=X.
- Parents exist because N_{k-1} is an s_{k-1}=2s_k net.
- Vertices are (x,s_k) for x∈N_k, and the root is o=(x0,1).
- Regular edges join (x,s_k) to (p_k(x),2s_k), for k=1..m. Bottom edges are [(x,0),(x,s_m)] for x∈X.

Abstractly the edges form a rooted tree: every non-root vertex has exactly one parent edge. Distinct abstract vertices sit at distinct points, because they differ in height or in projection. I verified the basic properties:

- G is connected and contains X×{0}.
- Projections are convex combinations of two points of X, so they lie within 1 of x0. Heights lie in [0,1]. So G⊂B(o,√2).
- Each regular edge has length ≤√5·s_k, which gives the stated L.

**Edge geometry.** Write a point of a regular edge of scale s with lower endpoint x as ((1−θ)x+θp, (1+θ)s). Its horizontal offset from x is θ‖p−x‖≤2s, and its height lies in [s,2s]. A ball intersected with a segment is a convex sub-interval of length ≤2r. Two balls of radius r/2 centered on that sub-interval cover it (centers at L/4 and 3L/4). The candidate's 8 is therefore a safe overcount, and it also handles open-ball conventions.

**Packing.** B_X(x*,R) with x*∈X is covered by D^q X-balls of radius R/2^q. If 2R/2^q≤s, each such ball holds at most one point of a >s-separated set. The candidate always chooses x*∈X, as this requires.

**Bottom portion.** If ‖(x,t)−(p,h)‖≤r then ‖x−p‖≤r. So the projections lie in B_X(x*,2r), which D^4 balls of radius r/8 cover. The heights lie in an interval of length ≤2r, which 16 pieces of length r/8 cover. A group then has diameter ≤√((r/4)²+(r/8)²)=(√5/8)r≈0.280r<r/2, so any member of the group is a valid center. Total: 16D^4, for every h and every s_m.

**Low center, h≤2r.**

- A meeting regular edge has height ≥s within r of h, so s≤h+r≤3r.
- *Fine edges, s≤r/64.* Every point of the edge is within √8·s≤(√8/64)r≈0.0442r<r/16 of (x,0). So ‖x−p‖<17r/16, and all such x lie in B_X(x*,17r/8)⊂B_X(x*,4r). Nine halvings give D^9 balls of radius r/128. Two points in one group are within 2(r/16)+2(r/128)=9r/64<r/2. Total: D^9. This step does not use separation, so mixing scales is harmless.
- *Intermediate edges, r/64<s≤3r.* The max/min ratio is <192<2^8, so there are at most 8 dyadic values.
  - At a fixed scale, ‖x−p‖≤2s+r. So the endpoints lie in B_X(x*,4s+2r), and since r<64s this radius is <132s.
  - With q=9 halvings, the covering-ball diameter is <264s/512<s. N_k is >s-separated, so there are at most D^9 edges at that scale.
  - Total: 8·D^9·8=64D^9.
- Sum: 65D^9+16D^4≤81D^10 for D≥1.

**High center, h>2r.**

- A meeting edge has 2s≥h−r and s≤h+r. Then (h+r)/(h−r)<3 holds exactly when h>2r, so the ratio 2(h+r)/(h−r)<6. That allows at most 3 dyadic scales; the candidate's 4 is a safe overcount. Also s>(2r−r)/2=r/2.
- Endpoints satisfy ‖x−p‖≤2s+r<4s, so they lie in B_X(x*,8s). Five halvings give diameter ≤s/2<s, hence at most D^5 edges per scale.
- Total: 4·D^5·8+16D^4=32D^5+16D^4≤48D^10.

**Exhaustiveness.** Every point of G lies on a bottom edge or on a regular edge of some scale k∈{1..m}. Each case above covers every meeting edge. No edge has its lower endpoint in N_0, so both the top root level and the last level are accounted for. Geometric crossings and overlaps only cause overcounting. The argument also holds for an arbitrary center in H⊕R, which is stronger than needed. Conclusion: G is Δ=256D^10-doubling in the ambient metric, and Lemma 1 holds as stated.

## Part 2 — witnesses, normalization, Dvoretzky (rederived; imports listed in contracts.md)

- **D=λ² for X_j.** An X_j-ball of radius r lies in an S-ball, which two halvings cover by λ² S-balls of radius r/4. From each one that meets the X_j-ball, choose a point of the intersection. The X_j-ball of radius r/2 at that point contains that whole part.
- **Normalization.** Rescaling diam X_j to 1 preserves doubling. It also preserves the obstruction, because the source's distortion definition has a free scale a.
- **Integrality.** λ²=5,898,240,000 is an integer, and Δ=256λ^20.
- **Dvoretzky.** span(G_j) is a finite-dimensional Euclidean space: G_j has finitely many vertices, and o_j∈G_j, so G_j−o_j⊂span. The classical Dvoretzky theorem, as cited by the source (`cor:banach`, [Dvoretzky §7], [COO Thm 1.1]), gives for every n a linear map ℓ_2^n→B with distortion <2. After rescaling, ‖u‖≤‖Tu‖≤2‖u‖.
- **Properties of Y_j.**
  - Y_j⊂B(0,2√2).
  - It is a finite union of segments, and its abstract edge-length sum is ≤2L_j.
  - It is Δ^4-doubling. A Y_j-ball of radius r pulls back into a G_j-ball of radius r. Four halvings give Δ^4 balls of radius r/16. Choose one point of the preimage in each, and every other point of that part maps within 2·(r/8)=r/4<r/2 of its image.

## Part 3 — curve, compactness, parametrization, doubling of Γ (rederived)

**Cluster placement.** Take C_j=a_jv+ρ_jY_j with 2√2ρ_j≤ηa_j and 2ρ_jL_j≤2^{-j}. Then C_j⊂B(a_jv,ηa_j), C_j is Δ^4-doubling, and its abstract edge-length sum is ℓ_j≤2^{-j}.

**Compactness.** Take a sequence in Γ. If infinitely many terms lie in I or in one fixed C_j, use that compact piece. Otherwise the cluster indices tend to infinity, and since ‖z‖≤(1+η)a_j→0, the terms converge to 0∈I.

**Parametrization.** Go down I from v. On first reaching a_jv, run a depth-first closed walk of the abstract tree of C_j, crossing each edge twice at unit norm speed.

- The breakpoints accumulate only at T=1+2Σℓ_j≤3.
- On [t_j,T), γ stays within (1+η)a_j of 0, so γ(t)→0, and setting γ(T)=0 is consistent.
- For s<t<T, only finitely many breakpoints lie between s and t, so ‖γ(s)−γ(t)‖≤t−s. Letting t→T extends this to t=T.
- The image is I∪⋃C_j=Γ: every tour covers every abstract edge, including the bottom edges. Rescaling to [0,1] gives a T-Lipschitz map, so H¹(Γ)≤T<∞.
- Overlaps make the abstract length sum an upper bound only, and the proof uses it only that way.

**Doubling of Γ.** Fix any center x∈Γ (on the spine, in a cluster, or at 0) and any r>0.

- I∩B(x,r) is a convex sub-segment of length ≤2r. Two (≤5) balls of radius r/2 centered on I cover it.
- Clusters with a_j≤r/4 lie in B_Γ(0,r/2), because (1+η)/4=101/400<1/2. The center 0 lies in Γ but need not lie in the ball, which the target allows.
- For i<j, ‖p−q‖≥a_i(1−η)−a_j(1+η)≥(1/2−3η/2)a_i=(97/200)a_i, using a_j≤a_i/2.
  - If ≥2 clusters with a_j>r/4 meet the ball, then a_i≤400r/97. The ratio is then <1600/97<32, so there are at most 5 dyadic scales.
  - If only 1 such cluster meets, its scale is unrestricted, which is fine.
  - Each such cluster portion lies in B_{C_j}(y_j,2r). Two Δ^4-halvings give Δ^8 balls of radius r/2 centered in C_j⊂Γ.
- Total: 2+1+5Δ^8≤6+5Δ^8≤Λ=10+6Δ^8. This is a finite integer, independent of B, j and the witnesses.

## Part 4 — nonembedding (rederived)

- **Zero-dimensional target.** It is impossible, because Γ⊃I has more than one point.
- **Positive dimension.** Compose with a linear isomorphism onto Euclidean R^k; equivalence of norms makes this bi-Lipschitz, giving a finite distortion A. Choose an integer j≥max(k,2A).
- **The contradiction.** X_j×{0}⊂G_j isometrically. The map u↦a_jv+ρ_jT_j(u−o_j) has distortion ≤2. Compose it with the restricted embedding and the isometric inclusion R^k⊂R^j. The result is an embedding of X_j into R^j with scale aρ_j and distortion ≤2A≤j, which contradicts the choice of X_j.

## Findings

**Mathematical gaps: none.** I tried to break each clause listed in the brief and could not:

- constants and endpoints;
- scale counts;
- arbitrary and inside-edge centers;
- segment intersections;
- the last level and the top root;
- tours versus Hausdorff length;
- centers outside the ball;
- all r;
- the zero-dimensional target.

Editorial repairs (non-blocking; the author packet must not be changed under this review):

1. **Ball convention.** State the convention. Every estimate is strict or overcounted, so closed and open balls both work.
2. **Safe overcounts.** The high-center case has ≤3 scales (written as 4), and an edge portion needs 2 balls (written as 8).
3. **Dvoretzky.** State it as the classical theorem for all ℓ_2^n, applied with n=dim span(G_j)≤dim span(X_j)+1. Do not write "the same theorem used by the source" as if the source applied it to this span.
4. **Abstract tree and length.** Define the abstract tree explicitly: vertices (k,x) and bottom vertices (x,0). Say that ℓ_j, L_j are abstract edge-length sums, not H¹.
5. **Spine count.** On the spine, 2 balls suffice, so 2+1+5Δ^8 is the sharp form of the stated count.

**Imported or stipulated contracts** (contracts.md): source `thm:main` and the finite-witness extraction inside the proof of `cor:banach` are stipulated true at the pin. The classical Dvoretzky theorem is imported as cited by the source. Equivalence of finite-dimensional norms is standard. The source's Y_j transfer and cluster-separation arguments were reread and redone, not just imported.

## Tests (evidence only)

`checks/cdf098_check.py`, with output in `checks/cdf098_check.out`, does two things:

- **(A)** rechecks every numerical inequality above with exact rationals;
- **(B)** builds Lemma-1 graphs for 6 seeded random finite sets, in dimensions 2–20 with n=12–40, and tests the scale windows, endpoint bounds, fine-edge proximity, the scale counts, the radius √2, and greedy half-radius cover counts on sampled points over 360 random balls.

All checks passed, and the greedy cover maxima were 7–27. Finite checks are not a proof of the universal statement, and the verdict does not rest on them.

## Read limits

Exact extents are in contracts.md. In short:

- Read in full: candidate.md and original-scope.md.
- Source main.tex read: lines 30–52 (definitions and `thm:main`), 53–80 (strategy, lines viewed truncated at 200 characters), 81–136 (construction and the complete `prop:doubling` proof) and 412–492 (the complete `cor:banach` with proof). Line 28 (abstract) was seen through a grep hit.
- Source lines 137–411 were not read: the derivative nonembedding proof and `cor:lp`, whose statement was seen only through a grep hit at line 390. Their truth is stipulated.
- The primary PDFs and texts (Gupta–Talwar, Schul, Semmes) were not read. They are not proof premises.
- cdf098-contribution-r1 was not read.
