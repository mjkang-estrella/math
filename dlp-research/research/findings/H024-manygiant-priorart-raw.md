# Raw Factory Fable H024 many-giant review — acceptance scoped separately

TaskId: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h024-manygiant-priorart-fable-20261008-r1

Primary source/cost review, not automatically an accepted baseline. In particular,
finite measurements are not proved asymptotic/worst-case constants, the event
budget needs actual operation accounting, and small-prime tests cannot settle
reported 32-bit behavior. See H024-manygiant-coverage.md for accepted scope.

# H024 card C review: prior art and matched full cost (read-only)

Scope: card C only (H024-information-hybrids-raw.md lines 96–127), H019-xonly-baseline-screen.md, RESEARCH_LOOP.md, STATE.md. No edits, runs, children, or commits. Both primary sources were read in full text; details and access paths are at the end.

## Verdict in one paragraph

Card C's f=3 case is not a proposal; it is Galbraith–Wang–Zhang §3.1 ("grumpy giants with negation"), measured at about 0.90√q keys. Its f≥4 case is the open variant Bernstein–Lange flagged in 2012, and the one natural uniform shift rule (giant i starts at iQ with stride ±(M+i−1)) was already implemented by GWZ (Appendix B, without negation) and lost to two giants. So the card's "main unsupported assumption" is a known open problem with one recorded negative, not an unexplored gap. The strongest applicable known comparator in the high-memory regime is negated grumpy giants with block generation, at ≈0.90√q keys × (2.5M+S) per key, not the proved two-family 0.943√q that H019 uses. The best any fresh design can do is a constant factor: at most 0.74× the key count of that comparator (f→∞, perfectly disjoint channels), realistically 0.90–0.95× if a shift rule is found. Recommend updating the comparison, not labelling a discovery; the card's own park threshold (beat 0.90√q) is the right bar and must be a paired exact comparison on the same prime.

## 1. Exact constants and assumptions from the sources (replacing "about 0.9")

**GWZ 2017, §3.1, Tables 4–5 (negated grumpy giants).** Lists x(iP), x(Q+jMP), x(2Q−k(M+1)P); so b=(0,1,2), strides (1, M, −(M+1)), shifts c=0. Match recovery uses 2⁻¹ and 3⁻¹ mod N (their displayed union of four sets). Parameters: M=√(N/2) found best among {√(N/2), √N, √N/2}; α (halt bound, per-list length/√N) in 0.87–0.92 for the Table 4 run and 0.90–0.96 across runs; Table 4 c(t) = 6.00, 5.76, 5.47, 4.10, 2.56, 1.72, 1.20 at t = 0, 0.15, 0.30, 0.46, 0.61, 0.76, 0.91, so coverage grows at the counting bound (c(0)=6 ⇔ (2/3)T²) and loses ~10% to overlap. Integral estimate gives c ∈ [0.90, 1.14]. Table 5 (100 curves × 10⁴ DLPs per bit size, 28–32 bits): 0.8926, 0.9053, 0.8961, 0.9048, 0.9207 (std dev 0.006–0.008). Table 3 records 0.9* as conjectural, worst case ≤2.7√N, and "grumpy giants with block computation 0.36*" vs "interleaved BSGS with block computation 0.38" (both ×0.4 from Lemma 4.2 at k=ℓ=8, I=8M, S=0.8M). Units are generated points, the same unit as H019's key count.

The card says this constant is "still unverified". More precisely: it is measured on 5×10⁶ instances but unproved, and the 32-bit value (0.921) sits 3–4 std devs above the others; the same 32-bit bump appears in Tables 2 and 6, so it is probably a setup artifact rather than asymptotic drift, but it leaves ±0.02 on the 0.90. An exact integer coverage computation (below) removes this uncertainty for free.

**GWZ Appendix B, Table 6 (4 giants, no negation).** Giants at Q, 2Q, 3Q, 4Q with strides M, −(M+1), M+2, −(M+3), M≈0.5√N: 1.2867, 1.3002, 1.2926, 1.2944, 1.3150 vs 1.25 for two giants. "It seems that the 4-giants algorithm is not as efficient as the 2-giants algorithm." This is the concrete prior uniform shift schedule the brief asked for, and it fails. The negated version of this rule has never been reported.

**Bernstein–Lange §6.** Baby (0,0)+{0..n−1}(0,1); Giant1 (1,0)+{1..n}(0,n); Giant2 (2,0)−{1..n}(0,n+1); n≈0.5√ℓ; 23n²/8+O(n) = (0.71875+o(1))ℓ slopes for 1.5√ℓ multiplications (vs 0.5625ℓ for BSGS, 0.6753ℓ for rho). Average-case weights: 1.23046ℓ^1.5 at ℓ=65537 (n=146), 1.20545ℓ^1.5 at ℓ=1000003 (n=558, so n≈0.56√ℓ, not GWZ's 0.707√ℓ). Variants paragraph, verbatim: a 4-giants algorithm "two in one direction, two in the other, with computer-optimized shifts of the initial positions" outperforms 2 giants "for m≈√ℓ"; speculation of (0.5+o(1))m² slopes; "it is not clear how to choose the shift distances properly." The eprint (2012/294, July 2012) and the ANTS X published version have identical text; the 2012-07-09 slides add nothing. No shifts were published. Note BL's "outperforms" is coverage at a fixed budget m≈√ℓ, not an average-case constant.

**BL §5** is about exhaustive addition-chain searches for ℓ<128 (their Table 5 is the lexicographically maximal slope-count sequence, weight = Σ i(dᵢ−dᵢ₋₁)). It is relevant only as evidence that forced anticollisions (≥3m−1 for an m-addition chain) keep the Nechaev–Shoup bound from being tight; it says nothing about shift schedules.

**Card C's quoted numbers check out:** f=2 ⇔ GWZ Lemma 3.2 (2√2/3, proved; c(t)=2, α=1/2). Without negation f=3 bound (2/3)√(3q)=1.1547√q vs BL's 1.2055√q; coverage 0.71875 vs 0.75. With negation the counting bound (2/3)√(q/(1−1/f)) gives 0.943, 0.816, 0.770, 0.745 for f=2..5 → 0.667; worst-case at the bound √(q/(1−1/f)) = 1.414, 1.225, 1.155, 1.118 → 1.0. BL's "(0.5+o(1))m² best possible" is the no-negation statement; with x-only matching the analogous ceiling is m² slopes, which is the card's f→∞ limit.

**Later work.** Two bounded web searches plus the reference lists of both papers found no later multi-giant design or rigorous analysis of negated grumpy giants. That is absence of evidence, not a novelty certificate.

## 2. Does H019's 2.5M+S per key hold for f progressions at once?

Yes, at leading order, with these charges:

- **Offsets.** Each family needs its own full affine offsets u·sᵢG, u=1..ℓ: fℓ stored points and O(fℓ) full additions, plus sᵢG (≈2 log q ops each) and bᵢQ (small multiples). Setup O(f(ℓ+k+log q)) full operations; lower order iff fkℓ = o(√q).
- **Batching.** Montgomery's trick does not care which family a denominator x(Xᵢⱼ)−x(u·sᵢG) belongs to, so one batch of size k_tot = Σkᵢ per round u serves all families (same ℓ across families is simplest). The inversion term (ℓ+1)/(k_tot(2ℓ+1))(I−3M) amortizes better, not worse. Limiting cost per emitted key stays S + 5(ℓ+1)/(2ℓ+1)M → 2.5M+S.
- **Prefixes and overshoot.** Each family emits contiguous blocks of kᵢ(2ℓ+1) indices; the lists grow in lockstep blocks, so the counting bound's equal-length requirement is met up to O(fkℓ) overshoot keys (GWZ's "additive factor proportional to kℓ").
- **Exceptions.** x(Xᵢⱼ)=x(u·sᵢG) means bᵢQ+(cᵢ+m sᵢ)G=±u sᵢG, a direct solve; at most O(fℓ) dispatches per run.
- **Table.** One hash table; per key one lookup plus one insert, identical to two families. The label needs (family, index); log₂f extra bits. Same-family x-hits are only genuine solves (for bᵢ≠0: k = −(2cᵢ+(j+j′)sᵢ)/(2bᵢ)) or k-independent non-events (bᵢ=0), so there is no new false-positive path. Recovery needs (bᵢ∓bᵢ′)⁻¹, nonzero because |bᵢ| are distinct. Up to two scalar verifications, as in H019.

So the complete-work ratio against the two-family comparator is c_f/0.943 to leading order, exactly as the card assumes. **Memory is where the card is loose.** Average stored keys scale with c_f, but allocation is set by the worst case: for GWZ's negated grumpy that is ≤2.7√q (3α√q), nearly double the two-family √(2q)≈1.41√q. A design that actually approached the counting bound would have worst case √(q/(1−1/f)) < 1.41√q and win on both counts, but the only known instance does not. "Equal memory" must therefore be stated as equal worst-case allocation, or a memory cap with charged fallback.

## 3. Complete-work comparison (H019 model, s=S/M=0.8, units of (5+s)M·√q)

| Schedule | keys /√q | status | work | vs 2-family | vs negated grumpy |
|---|---|---|---|---|---|
| Interleaved negation BSGS (H019) | 0.943 | proved | 0.536 | 1.000 | 1.048 |
| Negated grumpy, GWZ shifts | 0.90 (0.89–0.92) | experimental | 0.512 | 0.955 | 1.000 |
| f=3 counting bound | 0.816 | unreachable floor | 0.465 | 0.866 | 0.907 |
| f=4 counting bound | 0.770 | floor | 0.438 | 0.816 | 0.855 |
| f→∞ limit | 0.667 | floor | 0.379 | 0.707 | 0.741 |

Negation rho is 0.886√q group operations with O(1) memory and a different per-step cost; not the equal-memory comparator. Everything in the table is the same algorithm class, same exponent, same memory order. A fresh design that reached, say, 0.85√q would be a 5–6% constant over the strongest known high-memory comparator and about 10% over the proved one. That is the realistic ceiling of this card by the loop's metric.

## 4. Gaps in card C

1. "f=3" is GWZ §3.1 verbatim; any f=3 work is tuning (s₁, s₂, c₂) of a published algorithm whose authors swept only M∈{√(N/2), √N, √N/2} with c=0.
2. The "no concrete uniform shift design yet" statement omits GWZ Appendix B, which is exactly such a design and a recorded negative (without negation).
3. "GWZ constant unverified" should read "measured, unproved, ±0.02".
4. The falsifier's budget "≈q per design" holds only for perfectly disjoint channels. Real designs cost ≈2·C(f,2)·L_max² insertions: ≈5q for negated grumpy at α≈0.92 (≈2.5×10⁵ at q=5×10⁴). Under a 1M-event cap that is ≈4 designs at q=5×10⁴ or ≈20 at q≈10⁴, not 20 at 5×10⁴.
5. No worst-case memory statement (see §2).
6. BL's 4-giant "outperforms" is a fixed-budget coverage claim, not an average-case constant; the card presents it alongside average-case numbers.
7. Closed-form overlap counting of progression sumsets is precisely what BL could not do; do not plan on it.

## 5. Exact cheap integer coverage test (no curve arithmetic)

Validity: an x-match is P=±P′, a purely scalar event, so coverage in Z/q is exact for any prime-order curve; only the O(fℓ) exceptional dispatches are curve-specific. GWZ note the same ("one can perform simulations in (Z_N,+)"). Unlike GWZ's sampling, this gives the exact average over uniform k with zero variance.

- **Input.** Prime q; design {(bᵢ, cᵢ, sᵢ)}ᵢ<f as closed forms in q (e.g. sᵢ = round(βᵢ√q)+γᵢ), round-robin interleaving, block size ignored (or set to the H019 block B to charge overshoot).
- **State.** Bitmap over Z/q, covered counter, scalar lists aᵢ(j)=cᵢ+j sᵢ.
- **Step** (append index j to family i): for every other family i′, every j′<L_{i′}, ε∈{±1}: set bit at (bᵢ−εbᵢ′)⁻¹(ε aᵢ′(j′) − aᵢ(j)) mod q. If bᵢ≠0 also set −(aᵢ(j)+aᵢ(j′))·(2bᵢ)⁻¹ for j′<j. Record uncovered fraction u_n after each key n.
- **Outputs.** Exact average keys E = Σₙ uₙ; worst case = first n with full coverage (memory); the c(t) curve.
- **Controls on the same prime.** (i) f=2, b=(0,1), s=(1, ⌈√(2q)⌉): E must equal (2√2/3)√q + O(1), using H019's L(2L−1) signed count. This is an exact harness self-test. (ii) GWZ negated grumpy b=(0,1,2), s=(1, M, −(M+1)), M=round(√(q/2)): expect ≈0.90√q, and this also settles the 32-bit drift question.
- **Pre-declared candidates.** (a) GWZ Appendix-B rule with negation, f=5: b=(0,1,2,3,4), s=(1, M, −(M+1), M+2, −(M+3)), M over a small declared set. (b) f=3 sweep over s₂∈{−(M+r)}, c₂∈{0, ⌊M/2⌋, …}. (c) f=4, one baby plus three giants. A second baby is useless (BL §6: baby–baby slopes repeat √ℓ times; here b=0 pairs are k-independent).
- **Gate.** Select on one prime ≈10⁴, validate on two fresh primes ≈5×10⁴ with no retuning. Pass only if E(candidate) ≤ 0.95·E(GWZ control) on all three and worst case ≤ control's worst case. Otherwise park, per the card's own rule.
- **Translation to complete work.** work ≈ E·(2.5M+S) + E·(lookup+insert) + O(f(k+ℓ+log q))·(I+2M+S) + ≤2 scalar multiplications; memory = worst-case keys × (abscissa + index + family) bits.

## 6. Recommended disposition

Update H019/H024 comparison tables to list two comparators: proved two-family 0.943√q and experimental negated grumpy ≈0.90√q (GWZ Table 5, worst case ≤2.7√q), both at 2.5M+S per key. Reclassify card C from "constant-factor survivor" to "tuning of a known open variant with one recorded negative", with the ceiling table above. If the loop still wants to spend events, the f=3 sweep plus the negated Appendix-B rule is the cheapest decisive run; the floors (0.816, 0.770) bound what it can return.

## Sources and access

- D. J. Bernstein, T. Lange, "Two grumpy giants and a baby", ANTS X, Open Book Series 1 (2013) 87–111, doi:10.2140/obs.2013.1.87. Read: https://msp.org/obs/2013/1-1/obs-v1-n1-p05-s.pdf (28 pp.), §5 pp. 101–104, §6 pp. 104–107. Eprint 2012/294 mirror https://cr.yp.to/elliptic/grumpy-20120709.pdf read for the §6 variants paragraph (identical). The eprint.iacr.org PDF itself returned a Cloudflare challenge page in this session. Slides https://cr.yp.to/talks/2012.07.09/slides.pdf checked, no extra detail.
- S. D. Galbraith, P. Wang, F. Zhang, "Computing elliptic curve discrete logarithms with improved baby-step giant-step algorithm", Adv. Math. Commun. 11(3) (2017) 453–469, doi:10.3934/amc.2017038 (preprint eprint 2015/605). Read in full: https://pdfs.semanticscholar.org/5753/7e7d4d08b6de01aa79717c4bb849e694958f.pdf (17 pp.). Cited: §2.1 Tables 1–2, §3 Lemmas 3.1–3.2, §3.1 Tables 4–5, §4 Lemmas 4.1–4.2, §5 Algorithm 3 and the 0.4 block factor, Appendix A, Appendix B Table 6.
- Earlier counting framework: Chateauneuf–Ling–Stinson, "Slope packings and coverings…", J. Combin. Des. 11 (2003) 36–50 (cited by both; not re-read here).

Not done: no numerical coverage run, no edits, no Lean, no delegated children. The arithmetic in §3 is a Python one-liner on published constants, not an experiment.
