# AB194 independent adversarial proof review — round 1

Author of record: Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT. Third-party sources remain private in the author packet and are not copied here.

**Verdict: PASS_FULL_AB194.** This is a proof verdict only. It is not a contribution, eligibility, substantiality or acceptance verdict, and it changes no campaign count.

Reviewed exact bytes: author manifest SHA256 `581d8051354ede8bed18853f82c8a87726df5223a7d912b7aa00054d87658481`, scope.json `8f3721124a0e1d78e567221d97f188e0416587bd6b40aeb7615f4346df7e6de3`, rank-isolation.md `35085a430f183cd16a4ee6dcd8eca293739a633e0df2da2c094f4dfbaaef7667`. Running `verify.py --anchor <manifest hash>` gave `INTEGRITY_ONLY`, 24 payloads, 9 pinned blobs, 3 primary PDFs. I also checked each of the 9 source blobs' git SHA-1 against the complete `sources/preprints-tree.json` (`truncated=false`) at pin `fd4aeeb2…eeb`, and all 9 matched. Identity is not proof. Every mathematical step below was re-derived independently.

## Exact target reviewed (unchanged)

For every prime p, every nonzero complete commutative Noetherian local ring (R,m,k) of characteristic p with d=dim R≥0, every finite free complex F in homological degrees 0..d with finite-length homology and H_0(F)≠0, and every 0≤i≤d:

  binom(d,i)·χ_∞^R(F) ≥ e_m(R)·β_i^R(F),

where β_i=dim_k H_i(k⊗_R F) and χ_∞^R(F)=lim_n p^{-nd} Σ_j(−1)^j length H_j(Φ_R^n F). No domain, reduced, equidimensional, CM, F-finite, perfect/infinite-residue-field, graded or exceptional-fiber hypothesis is used, and d=0 is included. I did not weaken the target, and the proof does not need any weakening.

## Part A — abstract estimate (the only new operation)

Claim: under the full hypotheses of source `thm:complex` (h≥1, alternating rank 0, entries in I^s), for every 0≤i≤h,
λH_0(F) ≥ μ s^h [ b_i/binom(h,i) − (C_h/s) Σ_j b_j ], with C_h depending only on h.

**A1. Roots.** H_i(x)=∏_{0≤j≤h, j≠i}(x+j) is monic of degree h with simple roots {0,−1,…,−h}∖{−i}. Ordered decreasingly, its h−1 consecutive root gaps are (−(j−1),−j) for j<i, (−(i−1),−(i+1)) for j=i, and (−j,−(j+1)) for j>i. Rolle gives at least one root of H_i′ in each open gap. Since deg H_i′=h−1, that is exactly one simple root ρ_j per gap. In all three cases −(j+1)<ρ_j<−(j−1), strictly; i=0 and i=h give only one of the patterns. The windows are open and finitely many (i,j) occur, so a margin δ_h>0 and a gap γ_h>0 between successive ρ_j depend only on h. For s>max(1/δ_h, 2/γ_h), any integers with |r_j−sρ_j|≤1 (nearest-integer rounding exists) are strictly decreasing and satisfy −(j+1)s<r_j<−(j−1)s. One threshold serves every i. The root-bundle lemma needs only strictly decreasing integers, so V of rank (h−1)! exists.

**A2. Sign: total degree.** The source's convention (complex.tex l.12–14) is that a cohomology group H^v of the term in homological degree k contributes to total degree k−v. The l-th E-layer of a twist of D=G⊗V has term V(l−ks)|_E^{b_k} in degree k. Mod length zero, its cohomology lies in the single degree v=#{j: r_j>l−ks}, or vanishes when l−ks is a root (source `lem:complex-root-bundle` together with `lem:complex-graded-comparison`).
- *l≥0.* If j≥k+1 then r_j<−(j−1)s≤−ks≤l−ks, so v≤k. When k≥h−1, v≤h−1≤k holds anyway. When k=0, r_1<0≤l. So every surviving E_1 term has total degree ≥0. The finite filtration of D/D(M) by l=0..M−1 gives λ𝓗_k(D/D(M))=0 for k<0. By `lem:complex-twist-maps` (j=0, M≥M_D), 𝓗(D(M))→𝓗(D) is zero, so 𝓗_k(D) injects into 𝓗_k(D/D(M)). Hence λ𝓗_k(D)=0 for k<0.
- *l<0.* If 1≤j≤k−1 then r_j>−(j+1)s≥−ks>l−ks, so v≥k−1. For k=0 this is vacuous. So every surviving term has total degree ≤1, and λ𝓗_k(D(−M)/D)=0 for k>1. Twist-maps with j=−M makes 𝓗(D)→𝓗(D(−M)) zero, so the connecting map 𝓗_{k+1}(D(−M)/D)→𝓗_k(D) is surjective. Hence λ𝓗_k(D)=0 for k>0. The indices are tight: degree ≤1 is exactly what k+1>1 needs.
- Together with the finiteness in twist-maps, this gives χ_λ(D)=λ𝓗_0(D)≥0. The two shifted long exact sequences are used correctly.

The source's own sign proof (complex.tex l.558–596) uses only "j≥i ⇒ r_j<−is" and "j≤i−1 ⇒ r_j>−is". These follow from the wider windows just as well, so the widening is legitimate. My check (E) confirms the widening is actually needed: for every 1≤i≤h with h≥2 and every tested s, the rounded H_i′ roots violate the source's narrower windows.

**A3. Layer identity.** Source eq:complex-sum-estimate, 0≤(h−1)!λH_0(F)+μΣ_k(−1)^k b_k Σ_{l=−ks}^{−1}∏_a(l−r_a), uses only additivity, `lem:complex-euler-comparison` (alternating rank 0) and root-bundle Euler values. It does not depend on where the roots sit. The signs agree: χ of V(a) in ranks is Σ_v(−1)^v rank H^v=∏(a−r_j), and degree k carries (−1)^k.

**A4. Asymptotics, uniform in k and i.** Put P_s(x)=∏(x−r_a/s) and P=H_i′/h. On [−h,0], |r_a/s−ρ_a|≤1/s with all roots in [−h,0] gives ‖P_s−P‖_∞≤(h−1)(h+1)^{h−2}/s. The left Riemann sum of P over [−k,0] with mesh 1/s has error ≤k·sup|P′|/s. So s^{−h}Σ_{l=−ks}^{−1}∏(l−r_a)=(H_i(0)−H_i(−k))/h+O_h(1/s), uniformly in 0≤k≤h and 0≤i≤h. For k=0 both sides are 0.

**A5. Nodes.** H_i(−k)=0 for k≠i, and H_i(−i)=∏_{j<i}(j−i)∏_{j>i}(j−i)=(−1)^i i!(h−i)!. H_i(0) is h! when i=0 and 0 otherwise. By alternating rank 0, Σ_k(−1)^k b_k(H_i(0)−H_i(−k))/h = −b_i·i!(h−i)!/h. Dividing 0≤(h−1)!λH_0−μs^h[b_i i!(h−i)!/h−O_h(Σb/s)] by (h−1)! gives coefficient i!(h−i)!/h!=1/binom(h,i). For s below the threshold s_0, take C_h≥s_0. Then C_h/s≥1, so the right side is ≤μs^h(b_i−Σb)≤0≤λH_0. For h=1 there are no roots and V=𝒪: 0≤λH_0−μ s b_1, so λH_0≥μ s b_1=μ s b_0, which is exact for both i. Part A is correct.

## Part B — passage to the full target

**B1. d=0.** F=F_0, χ_∞=length(F_0)=b_0·ℓ(R), e_m(R)=ℓ(R) (Hilbert–Samuel function eventually constant), and β_0=b_0. The two sides are equal. ✔

**B2. Minimality (d>0).** Over a local ring, F≅F_min⊕(contractible). F_min stays in degrees 0..d with the same homology for every Φ^n, so χ_∞ is unchanged and b_i(F_min)=β_i(F). Minimality is *needed*: entries of Φ^nF lie in m^{[q]} only if the entries lie in m. A unit entry stays a unit, and rank-inflating contractible summands would break any rank inequality. H_0≠0 gives b_0≥1. ✔

**B3. Domain with algebraically closed k, d>0.** k is infinite, so a minimal reduction I=(z_1..z_d) exists with m^q⊆I^{q−c} for q≥c. thm:length-inputs needs a complete domain, h=d>0 and a perfect residue field (algebraically closed suffices). It gives C=R_perf and λ satisfying the abstract hypotheses with μ=e(I,R)=e(R). Φ^nF is minimal with finite-length homology and b_0≥1. lem:perfection-finite-length (arbitrary finite-length M, given the limit), applied to M=H_0(Φ^nF), together with Roberts' theorem (eq:dutta-h0, via Ma Thm 2.4) and existence of χ_∞, gives λH_0(C⊗Φ^nF)=χ_∞(Φ^nF)=q^dχ_∞(F). The last equality holds because Φ^m∘Φ^n=Φ^{m+n}. Entries lie in I^{q−c}C, contractibility off V(IC) persists, and the ranks are unchanged. Alternating rank 0 holds because d>0 makes (0) non-maximal, so F_{(0)} is exact. Part A with s=q−c≥1 gives q^dχ_∞≥e(R)(q−c)^d[b_i/binom(d,i)−C_dΣb/(q−c)]. Divide by q^d and let q→∞. ✔ This matches source cor:dutta-domain line by line, with b_0 replaced by b_i/binom(d,i).

**B4. Arbitrary complete R (any residue field, non-domain, non-equidimensional, non-reduced).** lem:residue-extension (its char-p case is the equal-characteristic coefficient-field construction) gives a flat local R→S with mS=n, algebraically closed residue field, the same Hilbert–Samuel function, d and e. G=S⊗F is minimal (entries in n), Φ_S^nG=S⊗Φ_R^nF, and length_S(S⊗M)=length_R M, so χ_∞^S(G)=χ_∞^R(F) and the β_i are equal. Take a prime filtration of S with factors D_j=S/P_j. Tensoring the free complex gives short exact sequences of finite-length-homology complexes, so χ_S(Φ^nG)=Σ_jχ_S(D_j⊗Φ^nG). For dim D_j<d, BHM Thm 5.2 (cited by the source) gives O(p^{n·dim D_j})=o(p^{nd}). For dim D_j=d: D_j is a complete domain of dimension d>0 with algebraically closed residue field, D_j⊗G is minimal with the same b_i and finite-length homology, and D_j⊗Φ_S^nG≅Φ_{D_j}^n(D_j⊗G) with equal lengths over S and D_j. B3 applies, giving χ_∞^{D_j}(D_j⊗G)≥e(D_j)b_i/binom(d,i). Associativity in top dimension, e(S)=Σ_{dim D_j=d}e(D_j) with repetition, gives χ_∞^R(F)≥e(R)β_i/binom(d,i). B3 never assumes that R itself is a domain or equidimensional. Lower-dimensional components and embedded primes only feed the o(p^{nd}) error. The same filtration works for every i. ✔

**B5. Hidden hypotheses.** None found. F-finiteness, the perfect residue field and the Cohen–Gabber normalization are used only inside thm:length-inputs for the domains D_j with algebraically closed residue field, where they hold or are stipulated. CM, reducedness and grading never enter.

## Counterexample search

I found no counterexample. Sanity cases are consistent and some are sharp. For regular R with F the Koszul complex on a regular system of parameters, χ_∞=1=e and β_i=binom(d,i): equality for every i. For R=k[[x,y]]/(xy) with F: R→R given by x+y, χ_∞=e(x+y;R)=2=e(R) and β_0=β_1=1: equality. For a Koszul complex on any s.o.p. x, the inequality reduces to e(x;R)≥e(R). Dropping minimality fails, as B2 explains, and the target correctly uses β_i.

## Classification of remaining issues

**Mathematical gaps:** none.

**Presentation issues (non-blocking; recommended for any manuscript):**
1. rank-isolation.md says "Choose a parameter reduction I of m". It should say a *minimal* reduction generated by d elements, which exists because the residue field is infinite, with c the reduction number (m^q⊆I^{q−c}, q≥c). This is the source's wording in cor:dutta-domain.
2. It should state explicitly that the abstract theorem is applied with s=q−c only for q>c, and give the explicit O_h bounds from A4 (the ‖P_s−P‖ and Riemann-sum constants) instead of "elementary".
3. The lower-dimensional filtration error should cite BHM Thm 5.2 (via the source) by name rather than "the exact Frobenius-homology estimate".
4. The text should note that the source sign proof only ever used the wider inequalities. This makes clear that A2 is a re-verification and not a new homological argument. The new content is the polynomial H_i and the node evaluation.
5. "Localizing the original short complex at the fraction field" should note that this needs d>0, which the proof assumes at that point.

**Inherited source premises (stipulated, not audited):** thm:complex standing hypotheses and lem:acyclicity, graded-comparison, twist-maps, euler-comparison, root-bundle; thm:length-inputs (Kurano–Shimomoto/Cohen–Gabber, CLMST normalized length); lem:perfection-finite-length; eq:dutta-h0 (Roberts via Ma Thm 2.4); existence of the Dutta limit (IMW 2022 §4.17, via the source); BHM Thm 5.2 low-dimensional bound; lem:residue-extension. Standard facts used without citation: decomposition into minimal plus contractible complexes, existence of minimal reductions over infinite residue fields, and top-dimensional additivity of Hilbert–Samuel multiplicity.

## Factual observation for the separate contribution gate (no verdict)

A2's widened windows are exactly the inequalities the source's sign proof already uses. The non-domain/arbitrary-residue passage (B4) is the source's cor:dutta-domain proof unchanged. The new mathematics is the choice of H_i, so that the cardinal interpolation at the nodes isolates b_i with weight 1/binom(h,i), and the observation that its derivative roots fit the sufficient windows. Whether this is substantial is for the contribution reviewer.

## Checks and limits

`checks/root_window_check.py` (MIT) uses exact rational arithmetic for 1≤h≤10 and all 0≤i≤h. It checks (A) the Rolle windows for the H_i′ roots via bisection, (B) the node identity coefficient by coefficient on the alternating-zero hyperplane, (C) for s∈{s_0,4s_0,16s_0,64s_0}, that the rounded roots are distinct and inside the windows and that the layer-degree conditions hold for all k and all l∈[−(h+2)s,(h+2)s], (D) that s·|layer-sum − integral| stays bounded as s grows, and (E) that the narrow source windows fail for i≥1. Result: `ALL_CHECKS_OK`, 0 failures (`checks/root_window_check.out`). This covers finitely many (h,i,s) and is supporting evidence only. The proof is A1–A5.

Read extents and contracts are in `contracts.md`. Hashes are in `reviewed-hashes.json`. Integrity: run `python3 -I verify.py --anchor <SHA256 of manifest.json supplied by the parent>`.
