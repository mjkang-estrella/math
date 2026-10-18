# T025O54 independent full-scope proof review, round 1

Reviewer role: independent FULL-SCOPE PROOF correctness only. This report does not assess contribution, novelty or acceptance. I did not read any parallel review, the parent intake directory, or any other T025O review material.

## Verdict

**PASS_FULL_T025O.** Relative to the stipulated source025 theorems at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, the frozen author proof (`candidate-proof.md` + `constrained-descent.md`) establishes the unchanged frozen target:

> There exist absolute C>0, b0>=3 such that for every odd b>=b0 and every integer 1<=a<b (not necessarily reduced), a/b = sum_{j<=k} 1/n_j with distinct odd 3<=n_1<...<n_k and k<=C log log b.

No exceptional numerators, subsequence of b, repetition, averaging or enlarged budget is used. Every interface the dispatch listed was rederived below from the actual operative source text. I found **no REQUIRED objection**. The twelve optional items in the last section are clarity or credit improvements; none is needed for correctness.

Packet identity: all seven external SHA256 anchors match. The author `verify.py` (read before running, read-only) returns `PASS_EXACT_INVENTORY` (37 files, 5 directories, 12 source blobs, 8 primary bodies) on the frozen packet and on a `/var/tmp` copy. The copy rejects a wrong anchor and a payload mutation. My own check recomputes all 12 non-PDF source025 Git blob identities against the repository's `sources/preprints-tree.json` (SHA256 `eeecc1da…dc5e09b`, 13223 entries, `truncated=false`). None of this is mathematical evidence.

Source theorems used (stipulated true, statements read): `residues.tex` Lemma `lem:discrepancy` (form and Erdős–Turán convention), `lem:reciprocal-phase` (B>=4 fixed, real Z, U^4<=|Z|<=U^B, I⊂[U,2U]), `lem:deterministic` (its proof is re-run with a new Z), the construction and endpoint facts `eq:level-endpoints`; `random.tex` Lemma `lem:random` (its proof is re-run at a larger modulus); `divisors.tex` Lemma `lem:divisor` (fixed D,r; S/(2logS)<=logX<=DS, X^{1/2}<=Y<=X, N<=e^{DS}); and the `descent.tex` recurrence mechanism. I checked the `elementary.tex`, `counting.tex` and `prescribed.tex` companions for interfaces. The proof never invokes `lem:distinct` or `lem:marked-cleanup`, which are the steps that break oddness, nor any rational-divisor supply.

## 1. Odd prefix (candidate-proof §1)

* **Harmonic prefix.** We have 1/3+…+1/13 = 0.955… < 1 < 1/3+…+1/15. Since a/b<1, at most six reciprocals are subtracted, and the first refusal happens at some odd d<=15. Then r<1/d<=1/3 and r<1/d_i for every prefix denominator d_i<d. Unreduced bookkeeping (A,C)->(dA-C,dC) gives C<=135135·b and A<C/3.
* **Odd greedy.** Let n be the least odd integer >=1/r. Then n<1/r+2 strictly (equality is impossible: if 1/r is an odd integer, n=1/r). So 1/n>r/(1+2r), and r'=r-1/n<2r^2/(1+2r)<=2r^2, i.e. y'<=y^2 for y=2r. Also r'<1/(n-2)-1/n=2/(n(n-2))<=1/n since n>=5 (n is odd and >1/r>3). Hence the next n exceeds the current one. The first greedy n is odd and >=1/r>d, so it exceeds every harmonic-prefix denominator.
* **Bookkeeping.** A'=nA-C<(C/A+2)A-C=2A and C'=nC<=C(C+2), since A>=1.
* **Stopping at T=b^{2D_C}.** Before crossing, r_j>=1/C_j>1/T while r_j<=(1/2)(2/3)^{2^j}. Hence j<=log_2(log T/log 1.5)+1=log_2 log b+O(1). At the crossing T<=C<T^2+2T. Also A<=45045·b·2^j=O(b log b)=b(log b)^{O(1)}, and A>=1 unless the expansion already terminated, which is a complete short odd expansion.
* **C is odd** (b and every multiplier are odd). With S=log C/(1.5D_C), (4/3)log b<=S<(8/3)log b+o(1), and C=e^{1.5D_CS} is trivially inside [e^{1.4D_CS},e^{1.6D_CS}]. S depends on a only through C, and every threshold is stated in terms of S>=(4/3)log b, so b0 is uniform in a. A<e^S holds for large b because A=O(b log b) and e^S>=b^{4/3}.
* **The remainder A/C is strictly below every prefix reciprocal** (the last greedy step gives r'<1/n, and earlier remainders were already below the earlier reciprocals). This is the same "remainder smaller than every reserved reciprocal" device as `prescribed.tex` Lemma `lem:marked-greedy-prefix`, adapted to odd steps.

## 2. Marker prime and auxiliary integer (constrained-descent §2)

* PNT gives about S^2/(2 log S) primes in [S^2,2S^2]. Distinct primes >=S^2 dividing C number at most log C/(2log S)<=0.8D_C S/log S=o(S^2/log S). So an ell not dividing C exists **for possibly composite C**. Also ell>11 and ell<S^K, so ell is not 5, 7, a template prime (3, 7, 11), or any source prime (>=S^K).
* M0=7·5^a·∏(deterministic p_j)·∏(all random samples p_{i,j,ε}) with multiplicity. It is odd and ell-free. Every deterministic or random list entry divides M0 (sub-multiset of the factors, as in source `residues.tex`). log M0<=log 7+D0 log S+log 5+(2R+1)m(K log S+log 2)<=(2R+1)KS+O(S/log S)<D_MS, because (2R+1)K=200100<D_M=204204. Also M0>=∏p_j>=S^{Km}>e^S. (The sentence "even with the extra polynomial factor ell" is confusing because ell is not a factor of M0; see optional O2.)
* **Terminal templates.** I checked them in exact arithmetic: 2/7=1/7+1/9+1/33+1/693, 3/7=1/3+1/11+1/231, 4/7=1/3+1/7+1/11+1/231. Each template is distinct, odd, 5-free, with prime support {3,7,11}. Since 5^a>=S^{D_0}>=u, the digits satisfy j<=a, and ell^ν M0/(7·5^j) is an odd integer. The 5-adic valuation of every digit-j denominator is exactly a-j, so different digit levels never collide. The ell-adic valuation is exactly ν. The length is <=4(a+1)=O(log S). No duplicate removal is used.

## 3. Constrained residue step (constrained-descent §3)

* Put z=1+2ell k with k>=0. Then 0<=uz-Qt<δu ⇔ Qt/(2ell u)∈(k+(1-δ)/(2ell), k+1/(2ell)]. Since 0<(1-δ)/(2ell)<1/(2ell)<1, this means {Qt/(2ell u)}∈J=((1-δ)/(2ell),1/(2ell)] with k=⌊Qt/(2ell u)⌋>=0. So z>=1, z is odd, and z≡1 (mod ell), hence ell does not divide z. The endpoint 1/(2ell) is exactly the case h=0.
* **Discrepancy.** Erdős–Turán (absolute constant, any interval in [0,1), multiplicities retained) with H=⌈2ell e^{4ηw}⌉ and every |F_l|<=e^{-3ηw}/(2ell) gives discrepancy ≪ e^{-4ηw}/(2ell)+(1+log H)e^{-3ηw}/(2ell). Its ratio to |J|=δ/(2ell) is ≪ e^{-3ηw}+(1+4ηw+log(3ell))e^{-2ηw}→0, uniformly for ell<=2S^2, because w=m or w>=D_0 log S, so log S=O(w). Hence at least δ|T|/(4ell) indexed entries lie in J.
* **Identity.** uz=Qt+h gives u/(ell^νM0Q)=1/((ell^νM0/t)z)+h/(ell^νM0Qz). I verified this exactly on random instances. The ratio of the residual to the first term is h/(Qt). Qt>u holds in every use: at high levels Q=C>=e^{1.4D_CS}>X_0>=u; at middle and terminal levels t>=S^{Km}>e^S>=u. With h<u this makes the residual strictly smaller than the emitted reciprocal. Every later reciprocal is at most the residual, so the emitted denominators strictly increase along each chain, giving **internal distinctness** with no cleanup.

## 4. Fourier inputs and simultaneous realization (constrained-descent §4)

* **High levels (deterministic, no randomness).** The off-diagonal phase is e(Z/u) with Z=lC(t-t')/(2ell), which is real and generally not an integer. Lower bound: |Z|>=C/(2ell)>=e^{1.4D_CS}/(4S^2)>=e^{D_CS}=e^{4D_XS}>=U^4 for U<=e^{D_XS}. Upper bound: |Z|<=(H/(2ell))C e^{(K+1)S}<=e^{(1.6D_C+K+2)S}<=e^{2.4D_CS}<=U^{3D_C} for U>=e^{0.8S}. Dyadic U satisfy Y/2<=U<=X with Y>=e^{S-ηm}. So `lem:reciprocal-phase` applies with fixed B=3D_C (it explicitly allows real Z), each piece is O(U^{1-δ_B}), and the mean square is <=2^{-m}+O(e^{-cS})<=e^{-0.01m}. The diagonal 2^{-m} uses the distinctness of the 2^m subset products. Markov at threshold θ=e^{-3ηm}/(2ell) plus the union over l<=H<=3ell e^{4ηm} bounds the bad u by 12ell^3 e^{(10η-0.01)m}X_j<=X_je^{-0.008m}.
* **Random lemma at v=2ell u.** I re-ran every line of the `random.tex` proof. For D_0 log S<=V=log v<=2S (actually V<=S+O(log S) at middle levels and V<=m+O(log S) at terminal ones), s=⌊0.75V/(K log S)⌋ satisfies 0.74V/(K log S)<=s and 2s<=0.03S/log S<m/4, so the Hamming exception is <=e^{-m/16}. Exposure leaves U0 a product of m-2s independent uniform samples, and U1,U2 independent products of s fresh labelled samples each. The I- and J-samples at differing coordinates are distinct labels, so independence holds. Since l<=e^{0.005min(m,V)}<=v^{0.005}, the event q<v^{0.9} forces gcd(U0,v)>v^{0.095} and hence >=k0=⌈0.08V/((K+1)log S)⌉ hit samples. Primes in [S^K,2S^K] dividing v number <=V/(K log S)<=2S, and 2 and ell are never sampled. The union bound gives (m·2S/P)^{k0}<=S^{-(K-4)k0}<=e^{-0.076V}<=v^{-0.05}. When q>=v^{0.9}: fresh values are <=v^{0.7575}<q, so reduction mod q is injective, and atoms are <=s!/P^s<=S^{-(K-2)s}<=v^{-0.7252}. Then orthogonality on Z/qZ (valid for composite q, including factors 2 and ell) and Cauchy–Schwarz give <=v^{1/2-0.7}=v^{-0.2}. Total: e^{-m/16}+v^{-0.05}+v^{-0.2}<=e^{-0.01min(m,V)}. **The extension is correct**, and it is a parameter re-check, not new cancellation.
* **Middle levels.** min(m,V)>=(1-η)m. log H<=4ηm+O(log S)<0.005(1-η)m. The per-u failure probability is <=12ell^3e^{(10η-0.01(1-η))m}<=e^{-0.008m}, so E B_j<=X_je^{-0.008m} and P(B_j>X_je^{-0.001m})<=e^{-0.007m}. The union over d=O(log S) levels is o(1). Only block T_1 is used, and no independence across u or across levels is needed.
* **Terminal levels.** For S^{D_0}<u<=e^m, take w=log u<=min(m,V). Then log H<=4ηw+log(3ell)<=0.00043w<0.005w (using log S<=w/D_0). Per block, the failure probability is <=12ell^3u^{10η-0.01}<=u^{-0.009+6/D_0+o(1)}<=u^{-0.008}. The R=1000 blocks are independent for fixed u, giving <=u^{-8}, and Σ_{u>S^{D_0}}u^{-8}=o(1). ell is fixed (it depends only on C,S) before sampling. One realization therefore satisfies the middle-level and terminal requirements simultaneously; the high levels are deterministic.

## 5. Descent, common set and recurrence (constrained-descent §5)

* **Last level.** For u<=S^{D_0}, the templates apply. For S^{D_0}<u<=X_d, terminal steps give h<u^{1-η}. log u falls from <=m to <=D_0 log S in O(log S/η) steps, with strong induction on u. Distinctness comes from §3, and the C-factor is 1 here (C_d=1).
* **G_j.** G_j=G_{j+1} ∪ {u<=X_j : some index i has a constrained step with h∈G_{j+1}∪{0}}. Membership does not mention ν or M0, so **one set serves ν=0 and ν=1**. Rescaling inherited expansions by C_j/C_{j+1}∈{1,C} and step tails by zC_j/C_{j+1} keeps everything odd and ell-free (C is odd and ell does not divide C), so the valuation stays exactly ν. I verified the switch identity u/(ell^νM0C_j)=1/((ell^νM0/t)z)+(1/(zC_j/C_{j+1}))·h/(ell^νM0C_{j+1}). Length: <=d steps through levels, plus O(log S) terminal steps, plus 4(a+1) template terms, i.e. O(log S) with an absolute constant.
* **Recurrence.** For nonexceptional u∈H_j∩(Y,X], at least ρ|T|/(4ell) indices have h∈[0,ρu)⊂[0,Y], and each such h lies in H_{j+1} (if h were 0 or in G_{j+1}, then u would be in G_j). For fixed (h,i), u divides C_jt_i+h and u<=X, so there are <=d_X(N+h) predecessors; the congruence on z only removes predecessors. The hypotheses of `lem:divisor` hold with fixed D=2D_C+D_M+2 (N=C_jt<=e^{(1.6D_C+K+1)S}), log X_j∈[S/(2log S),D_XS] for j<d, and X_{j+1}>=X_j^{1-η}>=√X_j. Hölder with fixed r>=max(2,8K_d) gives Σ_{h∈H_{j+1}}d_X(N+h)<=Y e^{S^{1/4}/r}δ_{j+1}^α. Double counting (indices retained) gives
  δ_j<=e^{-0.001m}+ρδ_{j+1}+4ell e^{S^{1/4}/r}δ_{j+1}^α<=ε_0+e^{2S^{1/4}}δ_{j+1}^α,
  where the last step uses ell<=2S^2. Unrolling from δ_d=0 with α^d>=e^{-2d/r}>=S^{-2K_d/r}>=S^{-1/4} and exponent sum<=1/(1-α)=r gives δ_0<=d·exp(2rS^{1/4}-0.001mS^{-1/4})<=exp(-cS^{3/4}/log S)=o(S^{-A}) for every fixed A. All constants (K,R,D_0,η,D_M,D_X,D_C,K_d,r,D) are fixed before S, and the threshold depends only on them. ε(S) depends only on S.

## 6. Sparse-dilation merge and final assembly (candidate-proof §2)

* R=X_0/(ell A M0)>e^{D_XS-S-D_MS}/ell=e^S/ell→∞. g=largest odd integer <=R satisfies g>=R-2>=R/2. So n=gAM0∈[X_0/(2ell),X_0/ell].
* For the n-1 splits u+v=n: u<=n-1<X_0, and ell v<=ell(n-1)<X_0. The bad u number <=εX_0. Bad v inject into [1,X_0]\G via v↦ell v, so they also number <=εX_0. This uses **only cardinality**, not equidistribution. Since n-1>=X_0/(2ell)-1>2εX_0 once ε<1/(8ell) (true because ε=o(S^{-3}) and ell<=2S^2), a split with u∈G and ell v∈G exists.
* ν=0 for u/(M0C) and ν=1 for ell v/(ell M0C)=v/(M0C). Each list is internally distinct, and the lists are separated by ell-adic valuation 0 vs 1. The sum is n/(M0C)=gA/C. Multiplying every denominator by the odd g is injective, so distinctness survives regardless of whether ell divides g, and the sum becomes A/C. Every new reciprocal is <= A/C, which is below every prefix reciprocal, so the new denominators exceed all prefix denominators. All denominators are odd. Since the total is a/b<1, none equals 1, so all are >=3.
* Length: at most 6 harmonic terms, plus log_2 log b+O(1) greedy terms, plus 2·O(log S) merged terms, with log S<=log log b+O(1). That is <=C log log b with absolute C. Every numerator 1<=a<b is covered, b is not reduced, and the parity relation k≡a (mod 2) is automatic.

**Conclusion: every unchanged frozen quantifier follows.**

## 7. Alternative-route obstruction (not used by the proof)

I rederived it for (b+1)/(2b)=((b+1)/2)/b, which has reduced odd denominator b. With nondecreasing odd d_i, no partial sum equals 1/2 (the numerator parity argument). The gap before index i<=j is >=1/(2P_{i-1}). So d_i<2kP_{i-1}, giving P_i<=(2k)^{2^i-1}. At the first crossing, 1/(2P_j)<=s_j-1/2<=1/(2b), hence b<=(2k)^{2^k-1}. This is correct, including with repetitions. It shows that no constant-factor oddification of a bounded-length unrestricted expansion exists. It is **not** progress on the target and not a counterexample: it gives k>=log_2 log b-O(log log log b), which is consistent with the target. The same product recurrence is the source's own lower-bound argument (`elementary.tex`, proof of the lower bound; `counting.tex`, F(k) upper bound), and the unrestricted lower bound there already shows that the log log b order of the target is necessary. The proof of the target does not rely on this file.

## REQUIRED objections

None.

## Optional items (non-blocking)

* O1. The ν=1 expansions are exactly the ν=0 expansions with every denominator multiplied by ell, since u/(ell M0C)=(1/ell)(u/(M0C)). The "common G for both ν" is therefore automatic, and the merge only needs ell-free expansions for u and ell v. Saying so would simplify the exposition and make the actual mechanism (sparse dilation plus valuation separation) clearer. Proof-neutral.
* O2. §2 of constrained-descent: "even with the extra polynomial factor ell" should read "ell^νM0<=2S^2·e^{D_MS}"; ell is not a factor of M0.
* O3. Make the prefix constants explicit: at most 6 harmonic steps, C<=135135b and A<C/3 after them, j<=log_2(log T/log 1.5)+1, and A<=45045·b·2^j.
* O4. Define "successful entry" in §5 explicitly: positive z≡1 (mod 2ell) with h∈G_{j+1}∪{0} for membership, versus h∈[0,δu) for the degree count. Both readings make the proof work, but the text uses one word for both.
* O5. Replace N<=e^{(2D_C+D_M+2)S} by the actual bound N<=C e^{(K+1)S}, and name D=2D_C+D_M+2 as the fixed divisor-lemma parameter.
* O6. State ε(S) explicitly as d·exp(2rS^{1/4}-0.001mS^{-1/4})<=exp(-cS^{3/4}/log S); "o(S^{-A}) for every A" undersells it.
* O7. "At most 2S eligible primes dividing v" can be sharpened to <=V/(K log S). This is harmless.
* O8. Say explicitly that the templates need ell>11 and that ell is chosen before the random samples. Both are true but implicit.
* O9. In the high-level count, give the explicit constant (12ell^3 from H<=3ell e^{4ηm} and θ^{-2}=4ell^2e^{6ηm}).
* O10. Credit the alternative-route product recurrence to the source's own lower-bound proof (`elementary.tex`) and the F(k) bound (`counting.tex`). Note that the source's unrestricted lower bound already gives necessity of the log log b order for the odd target.
* O11. Cite `prescribed.tex` Lemma `lem:marked-greedy-prefix` for the "remainder below every reserved reciprocal" device used when appending the prefix.
* O12. The candidate-proof sentence "classes become v_ell(g), v_ell(g)+1" is correct, but multiplication by g is injective anyway, so the valuation remark is not needed for distinctness after rescaling.

## Strongest paid route and what remains new to this deduction

The paid route is source025 in full: unrestricted greedy preparation, the dense-family reduction by two summands (`elementary.tex`), the deterministic and random prime-product residue construction (`residues.tex`, `random.tex`), the shifted truncated-divisor moment (`divisors.tex`), and the exceptional-set recurrence (`descent.tex`). The companions supply the remainder-below-reserved-reciprocals prefix and markers/padding. The new deductions I audited are four: the odd-multiplier congruence z≡1 (mod 2ell) carried through every level at a 2ell discrepancy cost; the modulus extension to v=2ell u; the base-5 odd terminal; and the sparse-dilation merge separated by a growing marker prime. Whether these are substantial is the contribution reviewer's question, not this report's.

## Validation performed

* Independent reading of all operative source passages listed above (see `reading-limits.md`).
* `independent-checks.py`, whose output is in `independent-checks.json`, reports `PASS_INDEPENDENT_CHECKS`:
  * author anchors and 12 source blob identities against the repository tree;
  * exact rational checks of 15 constant-slack inequalities;
  * the 4 templates;
  * 105750 toy merge instances with ell=17, including g divisible by ell;
  * 20000 random constrained-step interval-equivalence and identity checks, compared against brute force;
  * 3000 odd-prefix runs with T=b^6 checking the monotonicity, numerator, crossing and step bounds;
  * small-k obstruction inequalities on 17 found expansions;
  * author verifier replay (positive, wrong anchor, payload mutation) on a `/var/tmp` copy.
* All of these are finite or byte checks. They are not proof of any asymptotic claim, and the verdict does not rest on them.
