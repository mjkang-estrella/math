# T024W52 independent full-scope proof review, round 1

Reviewer: independent review sub-agent (proof correctness only). Original prose CC BY 4.0. This is not an acceptance; the parent alone accepts. No contribution assessment was made or consulted.

## Verdict

**NOT PASS_FULL_T024W AS WRITTEN: one REQUIRED erratum (R1). No mathematical gap was found.**

R1 is a false justification for a hypothesis of a classical input (Section 3). The reviewer checked a correct replacement against retained primary text. With the R1 wording replaced, every deduction in the r53 chain that I re-derived (Sections 4–5) yields the unchanged frozen statement: for every real x tending to infinity, V(x+x/log x)-V(x) ~ V(x)/log x, with no exceptional endpoints, subsequence, averaging, two-sided order replacement, growing-H assumption or narrower nominee. The parent decides whether an author erratum of R1 is enough to convert this into PASS_FULL_T024W. This review neither weakens the scope nor asks for a weakening.

## 1. Integrity, performed before interpretation

* External anchors: all seven SHA256 values supplied by the parent matched the frozen r53 files before `manifest.json` was parsed (manifest, scope-status, candidate-proof, local-sieves, local-coverage, contribution-comparison, reading-limits).
* The packet `verify.py` was read in full before it ran. It is read-only, requires an external 64-hex anchor, and rejects symlinks, hardlinks, nested manifests and inventory drift. Run on a /var/tmp copy with the external manifest anchor, it returned PASS_EXACT_INVENTORY: 44 files, 9 directories, 13223 tree entries, 30 family entries, 22 source blobs and 5 primary bodies.
* Independent authentication did not reuse the packet inventory. `sources/preprints-tree.json` in this repository (SHA256 eeecc1da...5e09b, truncated=false, 13223 entries) is byte-identical to the packet copy. The two families contain exactly 22 non-PDF blobs: 10 in source024 and 12 in the direct weighted-fiber companion. Each retained body's git blob SHA-1 equals the tree SHA and the receipt. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb matches `sources/upstream.json`.
* Primary bodies were checked only by retained identities (SHA256 in primary-identities.json). Hashes certify bytes, not mathematics.
* The frozen packet was never written. All controls ran on /var/tmp copies.

## 2. What was re-derived (whole chain, every quantifier)

Parameters: Y=2x, h=x/log x, J=(x,x+h], and B, m, P, R, L, H formed from Y. H is fixed first, then Y tends to infinity, then H tends to infinity. Constants are uniform for x in [Y/4,3Y/4] and h comparable to Y/log Y.

### Stress point 1: local bad-normal-prime bound (2)

* The removed global sets beat the local scale uniformly for exp(B^36)<=S<=Y. The local right side is at least c z B^5 (log Y)^(-13/6). The smooth set is Z exp(-B log B /3)=Z(log Y)^(-log B/3), from the Ford Lemma 2.3 estimate. The high-Omega set is Z(log Y)^(1-10 log 2) B, an exponent of about -5.93. Squares of primes at least S contribute at most Z/S<=Z exp(-B^36). Each is o of the local scale, uniformly in S.
* Translated two-form sieve: I checked Ford 2023 Theorem 2.5 (sieve notes lines 976-1115). It allows arbitrary integer intercepts. For the translated forms n+u and bn+(bu+1), Delta=b and rho(p) do not depend on u. For p|b, rho(p)=1, so the middle bound gives the singular loss b/phi(b), not its square, exactly as claimed. Primitivity and admissibility are also invariant under translation. For an inadmissible pair one of the forms equals 2, which allows at most 2 inputs.
* Small feasible q-intervals: a nonempty interval has U=Z/b>=q>Z^{2/log_2 Z}. Hence log(l/b)>=(1/2)log U>=log Z/log_2 Z, and (4) follows: l B^3/(b(log Y)^2).
* Reciprocal bad-cofactor sums (3): the first kind uses the Euler product over primes up to S, with Rankin weight 3/2, together with squarefreeness above S, which the square removal supplies. That gives log Z (log S)^(-0.31). The second kind sums the double-exponential mesh pairs, at most B^2 of them, to give log Z B^2 (log S)^(-1/6). When S>Z only the first kind occurs, and log S<=C log Z excludes Ford's log S>(log Z)^6 branch. (2) follows.

### Stress point 2: hyperbola split (5)

* Exact formulas: for n=pn', phi(n)=(p-1)phi(n') if p does not divide n', and p phi(n') if p divides n'. Both are overcounted. The count is over all non-S-normal primes p of ANY preimage, so values whose preimages are ALL bad are included. No good witness enters, so there is no circularity.
* For p<=sqrt Y, the cofactor totient lies in an interval at height t>=sqrt Y/C with length about t/log Y>=t^0.9. The local order bound (1), from Ford Theorem 4 (see R1), gives C h W(CY)/((p-1) log Y). Partial summation of Ford Lemma 2.6 gives sum over bad p<=sqrt Y of 1/(p-1) << B^6 (log S)^(-1/6).
* For p>sqrt Y, the cofactor totient w is at most C sqrt Y. Then p lies in intervals at z=x/w>=Y^{1/2}/C>=Y^{2/5} of relative length about 1/log Y, so (2) applies. The distinct-totient reciprocal sum over w<=C sqrt Y is O(W(CY)B), by partial summation of V(t)<=tW(T)/log t. Conditions (a) and (b) of S-niceness cost Y(log Y)^(-2.396)B and YB/S^{1/2}, both below the local scale. (5) holds.

### Stress point 3: rough sieve and first simplex failure (7)-(8)

* For (7), Ford 2023 Theorem 2.4 applies with g(p)=1/p on (S,F] and 0 elsewhere. Then (Omega) holds with kappa=1 and an absolute B, |r_d|<=1 on any interval, and the level is F. The remainder sum is at most F<=T^{1/10}, which T log S/log F absorbs.
* Extracted m: Omega(v)<=5 log_2 v gives m<=F^{5B+o(1)}<=Y^{1/4+o(1)}, so h/m>=Y^{0.74} and F<=Y^{1/(20B)}<=(h/m)^{1/10}.
* Theta-mesh: dropped coordinates below sigma=log_2 S/B contribute at most alpha sigma<=omega^2/(100k^2)<omega/100. Hence at least two coordinates are retained, because a_1+omega/100<1. Also theta_1>=(1+0.9 omega)/alpha>sigma, so E_1>S strictly, and sigma<0.01 gives S<Y^{1/(20B)}, so F>S. Theta_1<=1 holds because q_1<=sqrt n. The mesh entropy (10k log k/omega)^k<=B^{k/2}<=(log Y)^{omega^2/3000} holds in the nontrivial regime. The trivial regime falls back to (1). The non-nice part is exactly (5) with (log S)^(-1/6)=exp(-omega^2 B/(600k^3 log k)). The nice part is h(log Y)^(-1-omega/4), where the -1 comes from the simplex sum and not from the interval length. (8) holds.

### Stress point 4: localized Ford Theorem 16 and Theorem 10 (9)-(12)

* (9): the first inequality with coefficient xi_0<=1.001 gives u_2<=xi_0 B/(a_1+a_2)<0.78B. With Omega(n)<=6B and n>=Y/4, this gives q_0>=Y^{1/2-o(1)} and n/q_0<=Y^{1/2+o(1)}, including the case q_0=q_1. Fixing phi(r) gives two prime intervals at height >=Y^0.3 of relative length about 1/log Y. PNT with error z exp(-c sqrt(log z)) gives << h/(phi(r) log Y).
* Operation dependence: I checked Ford's (4.8) argument (lines 1123-1178) and the Theorem 16 proof (lines 1676-1710). In both, the only step that depends on the interval is the count of q_0 for fixed (q_1..q_{j-1}, d). The prefix factor R_{j-1}, the eligible-d sum (Lemma 4.3 below Y_j, and Lemma 4.2 for the global eligible set above Y_j) and Corollary 3.5 / Lemma 3.10 are interval-free. Replacing the q_0 count by (9) multiplies each term by h/x. This is a factorized substitution. It does not claim equidistribution of a global exceptional set.
* Strict break q_{j-1}>q_j: for j>=2 it follows from (xi_j+a_1)x_j<xi_{j-1}x_{j-1}, using increasing a_r and xi. For j=1, x_1<xi_0/(a_1+xi_1)<0.73, which forces q_0>q_1.
* Budgets: the j=0 term uses (8) with omega=10^-4 e^{-m/40}. Then omega^2 B/(600L^3 log L)>=B^c, since 1-1/(20 lambda)=0.918. The high-Omega cost is (log Y)^(-0.396)B relative. The terminal case uses S=exp(B^100), with relative cost B^(6-100/6)=B^(-10.67). All of these are o(exp(-m/4)) with exp(-m/4)=B^(-0.409+o(1)), so they are absorbable for every 0<=Psi<=sqrt m. The terminal sum over k>Psi uses exp(-k^2/(4C)) with C=0.818<1.
* Lemma 6.2 and Theorem 10: with |theta|<=0.04, every Psi used is at most sqrt m. In parts (b)/(c), Psi=ceil(sqrt(2|theta|m))<=sqrt(0.08m)+1. In parts (a)/(d) with i>3 eta m, Psi^2<=2 theta^2 m(m-i)/i<=(2 eta/3)m. (6.17)-(6.20), Lemma 6.1 and the terminal-bin sum are geometric and interval-free. The trivial cases of (6.15) fall back to (1). Summing i<=m-P gives (12).

### Stress point 5: coverage and discarded tuples (13)-(14)

* Coverage is universal over preimages. Outside E_J, every preimage meets the simplex (10, Psi=P), the coarse bands (12, eta=0.04, alpha/alpha_theta->1), p_0>=Y^0.9 (the p_1 band with Omega(n)<=6B and v>=Y/4), P^+(a)<=p_L by ordering, and the a-size condition. The a-tail failure is counted through the exact value (p_0-1)phi(r), the PNT in the actual interval, supermultiplicativity, source projected-mass and smooth-cost. E_J explicitly contains values whose preimages are all nonbasic.
* Discarded TUPLES: failing full witnesses are counted. Thin slack (with u_0=B fixed), Omega(D_i), and normality and squares at i>=1 do not depend on p_0, so the p_0 count is replaced by h/(D log Y) with D<=exp((log Y)^0.8). The i=0 normality conditions on p_1..p_J are independent of p_0 in the same way. S_0-normality of p_0 uses (2) with S_0=exp(exp(B^{1/3})) in [exp(B^36),Y], giving a saving of B^5 exp(-B^{1/3}/6), which beats exp(O(m^2)). The i=0 squares involving p_0 use the global witness count with values <=Y. The extra factor Y/h, about log Y=e^B, is beaten by exp(cB/m^20), since B/m^20 grows faster than log B. All four good conditions are covered.

### Stress point 6: ordered collisions (16)

* Top layer: after sigma_1 and t' are fixed, the common product in (a/r,b/r] confines Q to an interval of length delta Z, where Z=Y/(r s_1# t')>=Q>=Y^{1/(8B)}. Then log(delta Z)>=log Y/(16B). For the forms n+u, A(n+u)+1, A'(n+u)+1, Delta=AA'(A-A') independent of u, and A!=A' because p_0!=q_0 (p_i!=q_i at the first unequal index). The sum over t' is unchanged. Every lower layer and the smooth-part sum are positive reciprocal sums that are uniform in sigma_i, so the factor delta passes through. At i=0 the common product is v/r in (x/r,(x+h)/r] with delta=h/Y. Canceled primes, grids, the D-sum and the tuple-recovery factors are unchanged multiplicative costs.
* For i>=1, p_0 is common to both tuples. For fixed suffix pair and intervening primes, p_0 lies in an interval of length h/(v^(i) prod(p_j-1)) at height >=Y^0.9, which gives the same convergent tail. The count is over ordered pairs of distinct tuples with recovered coordinates, not over collided values.

### Stress point 7: tuples to values and calibration (17)-(20)

* Finite-map lemma, applied to T_J, G_J, D_J, W=V cap J: coverage holds outside E_J. Each tuple value is a totient because w<p_R, and F(tuple)=phi(n) for the induced tuple. This gives (17) directly in J, without subtracting global formulas.
* (18): for fixed data in D_H(Y), the admissible p_0 are exactly the primes in (1+x/D,1+(x+h)/D], all above Y^0.9. Their count is (1+o(1))h/(D log Y) uniformly, with relative PNT error O((log Y)^2 exp(-c sqrt log Y)). Tuples correspond bijectively to (p_0, datum). M_1(Y;H)<<K_H G.
* (20): source Proposition mass with ambient endpoint Y and c=2 gives V(x)=(x/log Y)(M_1+E_H G), with lim_H limsup_Y |E_H|=0. The source's t=Y case together with Ford's lower bound gives M_1>=c_-G/2 for large fixed H and then large Y. The ratio of (19) to (20) has limsup_Y |ratio-1|<=C eta_H, and the left side does not depend on H. Continuity of the phase, a variable-H rate and interchange of limits are not used, and no global errors are subtracted.

## 3. Findings

### REQUIRED

**R1 (local-sieves.md Section 1, line 11; the only REQUIRED item).** The text says theta=0.9 is "admissible by the classical quantitative PNT". That is false. An error term z exp(-c sqrt(log z)), or a Vinogradov–Korobov error term, does not give pi(t+t^0.9)-pi(t)>>t^0.9/log t. Admissibility of 0.9 is a hypothesis of Ford Theorem 4 (Ford text line 137), and that theorem is the sole source of the local order bound (1). (1) is used in (5) for p<=sqrt Y, in the trivial branch of (8), and in the trivial cases of Lemma 6.2. Required correction: justify admissibility by Hoheisel–Huxley (theta>7/12), or by the Baker–Harman–Pintz value 0.525 that Ford records at text lines 134-136, followed by tiling. Tiling means splitting (t,t+t^0.9] into about t^0.375 disjoint intervals (u,u+u^0.525] with u in [t,2t], each containing >>u^0.525/log u primes. The reviewer verified this replacement. No other step changes.

### OPTIONAL

* O1: local-coverage.md Section 3 quotes the (a)/(d) choice as Psi=ceil(|theta| sqrt(m(m-i)/(2i))). The retained text extraction at Ford line 1858 is garbled and probably reads ceil(|theta| sqrt(2L_0(L_0-i)/i)). Under either reading Psi^2<=(2 eta/3)m<=m when i>3 eta m. In that range part (c) is also used when theta<-i lambda_i/L_0, with Psi<=sqrt(2|theta|m)+1. State both, or cite the PDF.
* O2: state explicitly that the trivial cases of Lemma 6.2 (6.15) and of Ford (4.3) are covered locally by (1).
* O3: Ford Theorem 4's proof is not in the retained text. Lines 133 and 320-323 call it a corollary of a "simple modification" of the proofs of Theorems 1-2. The dependency should be named as the published theorem statement, with implied constants depending only on theta and k and uniform in y>=x^theta.
* O4: Ford Lemma 4.1's displayed "+y/(log y)^2" term does not arise in its displayed proof. The local re-derivation needs no corresponding term, so the parenthetical "harmless h/(log Y)^2 remainder" can be dropped.
* O5: in (9), say that the count depends only on the value phi(r), so summing over (q_1..q_{j-1},d) as in Ford, rather than over r, creates no fiber multiplicity.

## 4. Reliance (classical, with hypotheses checked)

Ford "The distribution of totients" (retained text, identity 6a0612cb...): Theorem 1 (order); Theorem 4 (upper short-interval order; hypotheses theta admissible, y>=x^theta, x large; see R1, O3); Lemmas 2.2, 2.3 (smooth estimate), 2.6, 2.7, 2.8 proof structure; Definitions 1-2; Lemmas 4.1, 4.2, 4.3, (4.6), (4.8), (4.10); Theorem 16 and its proof; Lemmas 6.1-6.2; Theorem 10 proof; Corollary 3.5, Lemmas 3.1, 3.7, 3.8, 3.10 as invoked inside Ford's own proofs (statements not re-audited). Ford 2023 sieve notes (identity 73131625...): Theorems 2.4, 2.5 and conditions (Omega), (Omega_0). Prime number theorem with classical error term (Tao notes not opened in this round). Stipulated source024 statements and the displayed proof internals: Lemma sieve, Proposition comparison and proof layers, Proposition collisions proof, finite-map lemma, Propositions basic, discard (including its i=0 square sub-bound), mass, (cofactor-size), (projected-mass), (smooth-cost).

## 5. Exact reading limits

* r53 packet, read in full: candidate-proof.md, local-sieves.md, local-coverage.md, scope-status.md, reading-limits.md, verify.py, manifest.json, primary-reading-ranges.json, primary-identities.json, receipt JSONs (machine-checked).
* Not opened, by role: contribution-comparison.md (hash only), checkpoint.md, chronology.md, the parent intake t024w-parent/intake.json, and any parallel review.
* source024, read in full: statements.tex, extraction.tex, layers.tex, collisions.tex, limits.tex. Not read: companion.tex, introduction.tex, main.tex, README.md, references.bib. The weighted-fiber companion: identity only; no body read in this round.
* Ford text, read: lines 60-239, 310-574, 930-1229, 1655-1989. This includes every pinned range: 1109-1178, 1661-1710, 1822-1964 and 1966-1976. Not read: 1-59, 240-309, 575-929 (Section 3 lemmas, relied on only through Ford's own proofs), 1230-1654 (Section 5 lower bounds), 1990-2563. PDFs were not rendered.
* Ford 2023 sieve text, read: lines 780-1124 only. The definitions of (g), (r) and (V) before line 780 were not re-read; they are assumed standard (multiplicative g in [0,1), remainder r_d).
* Tao PNT HTML: not opened.

## 6. Scope statement

This report audits only the proof correctness of the frozen r53 deduction against the unchanged r52 target. It makes no novelty, contribution or acceptance claim, and the author's technical recommendation was not used as evidence. Hashes and finite diagnostics are not proof. Third-party bodies were not copied into this directory.
