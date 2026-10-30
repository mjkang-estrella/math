# T025O54 independent contribution and eligibility review (r1)

Myeongjin Kang; no affiliation. Original review prose CC BY 4.0. Original verifier and diagnostic code MIT. No third-party body is copied into this packet; source025, Elsholtz, Webb and Graham passages are cited by the frozen author packet's retained file and line, and secondary web pages by URL only.

**VERDICT: TECHNICAL**

The verdict applies to the exact, unchanged T025O54 target and is conditional on the separate full-proof gate finding the frozen deduction correct. This review gives no proof verdict and did not read the parallel proof review. It is not DUPLICATE, not INELIGIBLE and not BLOCKED. It is not SUBSTANTIAL under the campaign rule that routine transfers do not count. No acceptance, nomination or count change follows; the count stays with the parent (16/20 per brief).

## 1. Exact object reviewed

Frozen author packet `frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r54/`, treated as immutable. All seven external anchors matched before the manifest was interpreted:

| file | SHA256 |
| --- | --- |
| manifest.json | e32e49cd36807d4c18291bb60d45f6431e48fb0c61566bfcc6ca4f30a4c3ddd3 |
| scope-status.md | f6da553993dc03592a52711922035d412ca21b6840194fb4b3440e8e7415e0b6 |
| candidate-proof.md | 74217f39dd39087e9881c78048bf5ec1822218f4da997089feb36142265a9ef7 |
| constrained-descent.md | 4cdab2ae581fb42e4db335c41db32e797285c91fcf7669535e1900eded11a636 |
| contribution-comparison.md | 2282e8107869ac40d9393a328ab3f2ff64e85cb89f209ae02b65e80ca3adbac7 |
| reading-limits.md | a78dca74d4d00b5bd8c5bf3e803f90ec789e28ed751331a45a248568685cba43 |
| alternative-route.md | 829fe320bb5e293ee22325373b667fbcec9489f637491b07c31491c9e873e932 |

Target (scope-status.md, kept unchanged): there are absolute C>0 and b0>=3 such that every odd b>=b0 and every integer 1<=a<b (not necessarily reduced) satisfy a/b = sum_{j<=k} 1/n_j with distinct odd 3<=n_1<...<n_k and k<=C log log b. There is no maximum-denominator restriction, exceptional numerator, subsequence of b, repetition, average-length or larger-budget substitute. Parity forces k ≡ a (mod 2) (clear the odd common denominator; each L/n_j is odd), and no exact k is prescribed.

Chronology accepted as disclosed: scope frozen 2026-10-18T17:12:49Z, after parity/terminal exploration and before the common-set/collision merge; author checkpoint 17:21:10Z. Earlier selection notes keep their temporal status. The parent intake is coauthor screening, not a review.

## 2. Integrity (identity only, never mathematics)

1. The author `verify.py` was read in full before running. It only reads and prints. Run in place with the external manifest anchor (`python3 -B`), it returned `PASS_EXACT_INVENTORY`: 37 files, 5 directories, 13223 tree entries, 15 family entries, 12 source blobs, 8 primary bodies. A whole-packet SHA256 snapshot taken before and after the run was identical.
2. Independently of the author verifier and its packet tree copy, I loaded the repository `sources/preprints-tree.json` (SHA256 eeecc1da…dc5e09b, 13223 entries, `truncated: false`) and `sources/upstream.json` (pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb). For all 12 non-PDF source025 receipts I recomputed the Git blob SHA-1 and SHA256 of the retained bytes and matched both against the canonical tree entry and the receipt. All 12 matched.
3. The 8 primary/derivative bodies match `primary-identities.json` by SHA256 and size. I did not re-retrieve them.

## 3. What the antecedents already pay, operation by operation

I read in full the source025 files listed in `reading-limits.md`, including both companions. Line numbers refer to the author packet's `private/source025/build/` copies.

**Source025 dense-to-every reduction** (elementary.tex 7–31 `prop:density`, 110–145 proof of `thm:main`). A greedy prefix prepares A/C, a dense set G of numerators u with short expansions of u/(MC) is built, n=gAM is split as u+(n−u) with both in G, and the two expansions are added and divided by g. Distinctness is restored at the end by `lem:distinct` (elementary.tex 33–61, Takenouchi), whose odd identity 2/(2p+1)=1/(p+1)+1/((p+1)(2p+1)) and even identity 2/(2p)=1/p destroy parity. This is the only step in the source chain that is unusable for odd denominators as it stands.

**Residue step and discrepancy** (residues.tex 1–30 identity (eq:residue-step), 207–238 `lem:discrepancy`). Erdős–Turán for an arbitrary interval J and any finite list, with the endpoint convention handled by rotation. The author's multiplier congruence z ≡ 1 (mod 2ℓ) is exactly this lemma applied to x_t = Qt/(2ℓu) and an interval of length δ/(2ℓ). I checked the equivalence exactly on 20000 random small instances (diagnostics.py); this is a sanity check of the bookkeeping identity, not a proof of anything asymptotic. The cost is a polynomial factor in ℓ<=2S² in the frequency cutoff and the threshold, absorbed by the source's exp(−0.01m) margins.

**Deterministic high levels** (residues.tex 240–358 `lem:reciprocal-phase`, which is stated for every real Z with U^4<=|Z|<=U^B; 360–402 `lem:deterministic`). The author's phase Z=lC(t−t')/(2ℓ) is real and nonintegral. The source lemma already covers real Z, so the only change is moving C into the interior range exp(1.4DC S)..exp(1.6DC S) so that the factor 1/(2ℓ) keeps |Z|>=U^4. This is a range adjustment.

**Random lists** (random.tex 8–156 `lem:random`, 158–256 selection). The source proof is stated for log u<=S. The author re-runs the same Hamming exception, the same exposure of two fresh groups, the same hit count, the same atom bound and the same bilinear orthogonality at modulus v=2ℓu with log v<=2S. Every exponent is a constant recheck (s<=0.75V/(K log S), 2s<m/4, at most 2S eligible prime divisors). The author itself calls this "a checked parameter extension, not a new cancellation theorem". I agree. At terminal levels, v<=2ℓe^m<e^S, so the source lemma applies verbatim; only the top sliver of middle levels needs the recheck.

**Exception recurrence** (divisors.tex 22–41 `lem:divisor`; descent.tex 71–245, from "Working backwards" through the unrolled recurrence). The predecessor count u | C_j t + h is unchanged; the extra congruence only removes predecessors; the successful degree drops from ρ|T|/2 to ρ|T|/(4ℓ), and the factor 4ℓ<=8S² is absorbed by exp(2S^{1/4}). The same Hölder recurrence follows.

**Superpolynomially small exceptional density.** The source's own proof already displays δ_0 <= d·exp(2rS^{1/4} − c_* m S^{−1/4}) (descent.tex 230–245, eq. density-unrolled), and only then weakens it to |H_0|<=X_0/8 (descent.tex 247). The author's ε(S)=o(S^{−A}) for every fixed A is therefore read off the source proof, with the harmless extra ℓ factor. This is the quantitative fact that pays for testing ℓv instead of v.

**Marker avoidance, internal distinctness and smallness-of-tail separation** (prescribed.tex 19–57 `lem:marked-greedy-prefix` with its strict inequalities R/q<1/n_i; 117–123 "Each reciprocal in this tail is at most its total … The tail therefore avoids the marker and all prefix denominators"; counting.tex 13–48 `lem:marked-cleanup`, preserving an odd divisor through cleanup). The author's two uses of "residual smaller than every earlier reciprocal" (inside each descent chain, where h<Qt makes the residual smaller than the term just emitted, and when appending the odd prefix) are this companion operation. In the source chain the same inequality h<Qt already holds; the source simply did not need it.

**Odd terminal digits.** The source's binary terminal stage (descent.tex 38–47) is replaced by base-5 digits with the explicit odd, 5-free templates d/7 (d=1..4) on support {3,7,11}. I rechecked the four identities, their distinctness and 5-freeness exactly. Distinctness across levels by 5-adic valuation is immediate. The operation "replace the binary remainder method by an odd-base remainder method" is the classical Breusch/Stewart construction for odd denominators according to a secondary description: Eppstein's annotated bibliography (https://ics.uci.edu/~eppstein/numth/egypt/refs.html, entries [Bre54], [Ste54]) says Breusch uses "a method similar to the binary remainder method but using the base 5(3^k)", and Stewart uses base 35(3^k). Neither original was read by me or the author (see reading-limits.md), so this attribution is secondary. In any case the author concedes the templates are elementary and not independently substantial.

**Separating two merged lists by a prime factor or congruence class.** Webb 1965 (webb.txt 46–55): in 1/b = s1/(P(s1Q+s2P)) + s2/(Q(s1Q+s2P)), "The denominators are not equal since P and Q have different prime factors". Elsholtz 2016 (elsholtz.txt 208–232): collisions in the odd/±1 mod P construction are repaired because the new denominators 3m_i, or (P²−1)m_i, lie outside the residue class 1 mod 3P(P²−1) occupied by the earlier ones. Separating two sublists by the exact ℓ-adic valuation of their denominators is the same device with a different marker.

## 4. The claimed bridge, examined directly

The contribution-comparison names the unpaid construction as a COMMON dense numerator set for the two auxiliary denominators M0 and ℓM0, with prescribed ℓ-adic valuation classes, together with a sparse-dilation collision-free merge.

**(a) The "common set for two valuation classes" is a rescaling, not a constructed invariant.** In constrained-descent.md every ν-dependent quantity is the factor ℓ^ν: the residue-step identity in §3 (denominator (ℓ^ν M0/t)z, residual h/(ℓ^ν M0 Q)), the digit multiplier ℓ^ν M0/(7·5^j) in §2, and the rescaled identity in §5. The chosen t, z and h, the good-set rule (G_j built from "h in G_{j+1} or h=0"), and the exception count do not depend on ν. Hence the ν=1 expansion of u/(ℓM0C) is, entry by entry, the ν=0 expansion of u/(M0C) with every denominator multiplied by ℓ. That is the identity x/ℓ = Σ 1/(ℓ d_i). Since every ν=0 denominator is ℓ-free (z ≡ 1 mod 2ℓ, ℓ ∤ M0, ℓ ∤ C), the ν=1 denominators have valuation exactly 1. The author's own sentence in §5, that the definition "contains no M0 or ν", records this. The diagnostics check the one-step identity and the entrywise ℓ-scaling exactly on random small instances. The algebra is immediate; the check is only a guard against transcription error.

**(b) The sparse-dilation merge is a union bound plus a marker.** Given the source's superpolynomial density (Section 3), the count of v with ℓv ∉ G is at most |[1,X]∖G| <= εX. That is far below n−1 ≍ X/ℓ because ℓ<=2S². So some split n=u+v has u ∈ G and ℓv ∈ G. The expansion of ℓv/(M0C), divided by ℓ, represents v/(M0C) with valuation-1 denominators; the u expansion has valuation 0; multiplying all denominators by the odd g shifts both classes by v_ℓ(g) and keeps them disjoint. Each step is two lines once the source density bound and the classical valuation separation are available. The growing size ℓ ∈ [S²,2S²] is forced only by the need for ℓ ∤ C with C arbitrary (C is divisible by b), and PNT prime avoidance is classical. The polynomial size makes the union bound and the ℓ³ Markov loss free.

**(c) Why it is not a direct source operation, and why that does not make it substantial.** The source never forms ℓv or imposes a multiplier congruence, because it can always fall back on Takenouchi cleanup. So the odd theorem is not a literal source corollary, and it is not a DUPLICATE. But the replacement for the cleanup uses no new estimate. It uses one classical separation device and a quantitative fact the source proof already prints. The modified descent changes moduli, intervals and ranges by factors polynomial in S, which the source's exponential margins absorb.

**(d) Route obstruction.** alternative-route.md correctly reports that naive post-hoc oddification of the unrestricted theorem cannot work. Its proof is the source's own product recurrence from the lower bound (elementary.tex 147–170, d_j<=sL_{j−1}, L_j<=sL_{j−1}^2) and from counting.tex's upper bound, applied at the first crossing of 1/2. It explains why oddness must be built into the descent from the start. Doing that is the finite-constraint bookkeeping above. The obstruction is not nominated and is not counted here.

**Genuinely modified pieces, listed exhaustively.** (i) The discrepancy interval and modulus at every level (u→2ℓu, length δ→δ/(2ℓ)). (ii) The random-product range log v<=2S. (iii) The interior C range. (iv) The odd terminal base. (v) The ℓ-dilation merge in place of Takenouchi cleanup. Each is a parameter change or a classical device. None is a new cancellation, divisor, sieve or combinatorial estimate.

## 5. Strongest paid route (cheapest complete route to the unchanged target)

Run source025's proof of Theorem 1.1 with these finite changes:

1. Use an odd greedy prefix in the manner of `lem:greedy` and `lem:marked-greedy-prefix`.
2. Choose a PNT prime ℓ ∤ C with ℓ<=poly(S).
3. Set M = 7·5^a·(source primes) and use the odd-base remainder digits in place of 2^a.
4. Apply `lem:discrepancy` at modulus 2ℓu with interval ((1−δ)/(2ℓ),1/(2ℓ)], so that every multiplier is odd and ℓ-free. Feed it with `lem:reciprocal-phase` (real Z, interior C range) and `lem:random` with its range rechecked.
5. Run the source recurrence with the extra ℓ in the degree.
6. Take the superpolynomial density from eq. density-unrolled.
7. Split n=u+v with u ∈ G and ℓv ∈ G, and divide the second expansion by ℓ. Use valuation separation, the odd g, and the prescribed.tex smallness argument for the prefix.

This route reaches the full frozen scope with no narrowing. It is exactly the author's construction, which is why the full proof, if it passes, is TECHNICAL rather than SUBSTANTIAL.

## 6. Eligibility and history

* Eligible as a target: it differs from the I204/I205 polynomial maximum-denominator target (i204-arithmetic-structures-discovery.md 17–30; i205 parent disposition), which stays unresolved and is not renamed. A grep of all non-private project Markdown, JSON and text for odd-denominator Egyptian expansions found no earlier T025O development. Fixed markers, padding, rational-divisor supply and the I205 divisor-split cleanup are already developed and are not counted.
* Not a pre-source duplicate on available evidence: source025's introduction (introduction.tex 13–45) records Vose's √log b as the best uniform bound before the source. Any earlier odd-denominator O(log log b) bound would have settled Erdős Problem 304 for odd b, and no such record appears in that account or in the searches below. Breusch/Stewart, Graham 1964 (pp. 206–207, item (1)), van Albada–van Lint and Webb are existence results, and Elsholtz 2016 counts expansions of 1. Results after September 2026 are not excluded beyond the bounded searches.
* The bounded searches found no odd-denominator uniform length theorem (queries and pages in reading-limits.md). This is not a worldwide novelty certificate.

## 7. Required objections (numbered)

R1. **Reclassify the contribution as TECHNICAL.** contribution-comparison.md must stop presenting the "COMMON dense numerator set for two auxiliary denominators" as a constructed invariant. The ν=1 expansions are the ν=0 expansions scaled entrywise by ℓ (Section 4a). Any manuscript must describe one dense set plus the identity x/ℓ = Σ 1/(ℓd_i).

R2. **Credit the exceptional density that pays the dilation to the source proof.** The bound ε(S)=o(S^{−A}) is source descent.tex eq. density-unrolled (lines 230–245), weakened only in the stated Proposition (line 247). The "small exceptional density on a sparse dilation" in contribution-comparison.md must cite it, and must not be part of the claimed unpaid bridge.

R3. **Credit the internal-distinctness and tail-separation invariant to the companions.** Credit prescribed.tex `lem:marked-greedy-prefix` (19–57) and its tail-avoidance paragraph (117–123), and the source's own h<Qt in eq. residue-step. The author currently presents "residual smaller than the first emitted reciprocal" as part of its construction without that companion credit.

R4. **Credit the valuation separation of merged lists as a classical device.** Credit Webb 1965 (webb.txt 46–55, separation by distinct prime factors) and Elsholtz 2016 (elsholtz.txt 208–232, residue-class separation of new denominators), together with counting.tex `lem:marked-cleanup`. The sparse-dilation merge must be described as a union bound with a marker prime, not as the substantive bridge.

R5. **Qualify the attribution of the odd-base terminal stage.** The odd-base remainder method is attributed to Breusch/Stewart only through a secondary source (Eppstein's bibliography), since the 1954 originals are unread. Any manuscript must say so and not present the base-5 replacement as a new operation.

R6. **Credit the route obstruction's method.** The (b+1)/(2b) obstruction in alternative-route.md is the source's product recurrence (elementary.tex 147–170; counting.tex upper bound) and must cite it. It stays a route obstruction, not a nominee or counterexample.

R7. **Keep the scope unchanged.** The TECHNICAL verdict does not license narrowing: no exceptional numerators, subsequence of b, repetition, larger budget, or reduced-fraction restriction may be introduced to manufacture substantiality. Any novelty language must be "bounded comparison; no worldwide novelty claim", listing the unread Breusch, Stewart, Sierpiński and Chen–Elsholtz–Jiang originals.

## 8. Optional suggestions

O1. The random-range extension to log v<=2S can be avoided by switching C_j to 1 at e^S/(4S²) instead of e^S. The source lemma then applies at modulus 2ℓu verbatim; only threshold bookkeeping changes.

O2. Stating the ν=1 case as the scaling corollary would shorten constrained-descent.md §1 and remove the impression of two parallel constructions.

O3. The parity remark k ≡ a (mod 2) is correct and could be stated with its one-line proof.

## 9. Bottom line

Conditional on the separate full-proof gate, T025O54 is a correct-looking odd-denominator analogue of source025 Theorem 1.1's upper bound. It is not a literal source corollary, so it is not a DUPLICATE. It is eligible and not blocked. But every modification is a finite congruence or valuation constraint, a parameter recheck, or a classical device, paid by the source's printed exponential margins and superpolynomial density. Contribution: **TECHNICAL**. The frozen target stays unchanged and unresolved for campaign-acceptance purposes.
