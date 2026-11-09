# CANDIDATE 336565: proof of the Liu–Ding trace-cubic 3-design conjecture (all m ≥ 3 with m ≢ 0 mod 4)

Lane: expanded-corpus-r163 (Claude Opus 5.5 discovery lane). Status: **ordinary proof complete; Lean NOT run in this lane (Claude lane restriction); draft Lean source `lean/LiuDing3Design.lean` is UNCOMPILED.** Zero credit unless root accepts.

## 1. Exact target and provenance

- MathDB 336565, "The 3-design conjecture for the trace-cubic design". Exact corpus line: `raw/336565.jsonl`; chunk, one-based line, chunk/raw/statement SHA-256 in `extracted.json`.
- MathDB literal text (abridged): "Let q = 2^m with m [≥] 3, let P = GF(q), and let 𝓑₂ = {u ∈ GF(q) : Tr(u³ − u) = 1}. **The trace-cubic 3-design conjecture.** If m ≢ 0 (mod 4), then the pair (P, 𝓑₂) is a 3-design. ... confirmed by Magma for m ∈ {3,5,6,7}". The "≥" was lost in the MathDB rendering ("m 3").
- Source: H. Liu and C. Ding, *Infinite families of 2-designs from GA₁(q) actions*, arXiv:1707.02003, version v1 (the only version, 7 Jul 2017; abs page fetched 2026-11-04, see `outputs/fetch-receipts.json`), **Conjecture 1** (pdf p. 15, directly after Theorem 21). The source text reads: "Let m ≥ 3 such that m ≢ 0 (mod 4). Then the pair (P, B₂) is a 3-design."
- Source convention (decisive for the literal reading): the paper's Corollary 2 and Theorems 4, 9, 12, 17, 23 all define the design as (P, 𝓑) with **𝓑 = GA₁(q)(B)**, the orbit of the base block B under x ↦ ax + b (a ≠ 0). In Theorem 21 and Conjecture 1 the calligraphic 𝓑₂ is that orbit of the base block B₂ = {u : Tr(u³ − u) = 1}. The source's Theorem 21 already proves that (P, 𝓑₂) is a 2-(2^m, k, λ) design, with k = |B₂| (Lemma 18) and stabiliser computed in Theorem 20. Read literally, the MathDB paraphrase "(P, 𝓑₂)" with 𝓑₂ a set of points is ill-typed. Source scope takes precedence: the target is the orbit design (GF(q), GA₁(q)(B₂)).
- Tr is the absolute trace GF(2^m) → GF(2). In characteristic 2, u³ − u = u³ + u.

## 2. Theorem proved

**Theorem.** Let m ≥ 3 with m ≢ 0 (mod 4), q = 2^m, Q(x) = Tr(x³ + x), B = {x ∈ GF(q) : Q(x) = 1}, and 𝓑 = {aB + b : a ∈ GF(q)*, b ∈ GF(q)}. Then (GF(q), 𝓑) is a 3-design: every 3-subset of GF(q) lies in exactly λ₃ blocks, where

- λ₃ = q(q − 4)/16 if m ≡ 2 (mod 4), with k = q/2;
- λ₃ = (q² − 3qs + 6q − 8k)/16 if m is odd, with s = q − 2k = ±2^{(m+1)/2}.

The values use |Stab(B)| = 2 (source Theorem 20). The 3-design property itself does not depend on the stabiliser value.

The proof also shows why m ≡ 0 (mod 4) fails, which matches the source's exclusion and our controls at m = 4 and 8.

## 3. Ordinary proof

Notation: χ(x) = (−1)^{Q(x)} ∈ {±1}, so 1_B(x) = (1 − χ(x))/2. Let s = Σ_x χ(x) = q − 2k with k = |B|, and S(a) = Σ_e (−1)^{Tr(a e³)}.

**Step 0 (blocks through a 3-set).** Let G = GA₁(q). The map G → 𝓑, π ↦ π(B), is surjective. Its fibres are left cosets of Stab_G(B), so each has size σ = |Stab_G(B)|. For a 3-subset T = {t₁, t₂, t₃}, therefore

σ · #{C ∈ 𝓑 : T ⊆ C} = #{(a, b) : a ≠ 0, T ⊆ aB + b}.

Now T ⊆ aB + b if and only if (tᵢ − b)/a ∈ B for i = 1, 2, 3. Put x = (t₁ − b)/a and d = (t₂ − t₁)/a ≠ 0, and let u_T = (t₃ − t₁)/(t₂ − t₁) ∉ {0, 1}. Then (t₃ − b)/a = x + u_T·d. The map (a, b) ↦ (x, d) is a bijection from GF(q)* × GF(q) onto GF(q) × GF(q)*. Hence

#{(a, b) : a ≠ 0, T ⊆ aB + b} = N(u_T) − k, where N(u) := #{(x, d) ∈ GF(q)² : x, x + d, x + ud ∈ B}.

The subtracted k is the d = 0 term. So (GF(q), 𝓑) is a 3-design if and only if N(u) is constant on GF(q) \ {0, 1}. (This is the same criterion as Tang, arXiv:1904.04071, Lemma 7 and Theorem 9; it is reproved here in three lines.)

**Step 1 (expansion).** For u ∉ {0, 1}:

8N(u) = Σ_{x,d} (1 − χ(x))(1 − χ(x+d))(1 − χ(x+ud)).

Expand the product and sum each term over all (x, d):

- The constant term gives q².
- Each single-χ term gives q·s, because for fixed d (resp. x) the argument runs over GF(q). There are three such terms, each with a minus sign.
- Each two-χ term gives s². The pairs (x, x+d), (x, x+ud) and (x+d, x+ud) are each a bijective linear image of (x, d), because u ≠ 0 and u ≠ 1. There are three such terms.
- The triple term is T(u) := Σ_{x,d} χ(x)χ(x+d)χ(x+ud), with a minus sign.

So 8N(u) = q² − 3qs + 3s² − T(u).

**Step 2 (the quadratic identity).** In characteristic 2, (x + y)³ = x³ + x²y + xy² + y³. Summing the three cubes gives

x³ + (x+d)³ + (x+ud)³ = x³ + (1+u)x²d + (1+u)²xd² + (1+u³)d³,

and the linear terms sum to x + (1+u)d. Put e = (1+u)d, which is a bijection in d since u ≠ 1. Then x³ + x²e + xe² = (x+e)³ + e³, so

Q(x) + Q(x+d) + Q(x+ud) = Q(x+e) + Tr(e³ + (1+u³)d³) = Q(x+e) + Tr(a·e³),

with a := 1 + (1+u³)/(1+u)³ = 1 + (1+u+u²)/(1+u)² = u/(1+u)². Note a ≠ 0 for u ∉ {0, 1}. Therefore

T(u) = Σ_e (−1)^{Tr(a e³)} Σ_x χ(x + e) = s · S(u/(1+u)²).

**Step 3 (m odd).** Since 2^m ≡ 2 (mod 3), gcd(3, q − 1) = 1, so e ↦ e³ is a bijection of GF(q). Hence S(a) = Σ_y (−1)^{Tr(a y)} = 0 for a ≠ 0, because Tr is a nonzero linear functional. So T(u) = 0.

**Step 4 (m ≡ 2 mod 4).** We show s = 0. First,

s² = Σ_{x,e} χ(x)χ(x+e), and Q(x) + Q(x+e) = Tr(x²e + xe² + e³ + e) = Tr(x(e^{2^{m−1}} + e²)) + Tr(e³ + e),

using Tr(x²e) = Tr(x e^{2^{m−1}}) (Frobenius invariance of Tr). Summing over x leaves only those e with e^{2^{m−1}} = e², that is e⁴ = e, so e ∈ GF(4) ∩ GF(q). This gives

s² = q · Σ_{e ∈ GF(4) ∩ GF(q)} (−1)^{Tr(e³ + e)}.

For m even, GF(4) ⊆ GF(q). The terms e = 0 and e = 1 contribute +1 each, since Tr(0) = 0 and Tr(1 + 1) = 0. For e = ω, ω² (the primitive cube roots of unity), e³ + e = 1 + ω = ω² or 1 + ω² = ω. Their trace is Tr_{GF(q)/GF(2)}(ω) = (m/2)·Tr_{GF(4)/GF(2)}(ω) = (m/2)(ω + ω²) = m/2 mod 2, which equals 1 when m ≡ 2 (mod 4). So s² = q(1 + 1 − 1 − 1) = 0, hence s = 0 and T(u) = 0. This step reproves the source's own Lemma 18 value k = 2^{m−1}.

**Conclusion.** In both cases N(u) = (q² − 3qs + 3s²)/8 is independent of u, so by Step 0 the orbit design is a 3-design. ∎

(For m ≡ 0 (mod 4): s ≠ 0 (s² = 4q), and S(a) depends on the cube class of a, so N(u) is not constant. This is consistent with the source's exclusion and with our computed controls at m = 4 and 8.)

## 4. Computational cross-checks (diagnostics, not proof)

- `scripts/design3.py`: Walsh-transform evaluation of N(u) for all u. It confirms the 3-design property for m = 3, 5, 6, 7 (the source's Magma range) and for m = 9, 10, 11, 13, 14 (new). m = 14 ran in four sequential u-chunks via `scripts/design3_chunk.py`. Controls at m = 4 and 8 are correctly NOT 3-designs. Logs: `logs/design3.log`, `logs/design3_m14.log`. N(u) = q²/8 for m ≡ 2 (mod 4), as predicted.
- `scripts/design3_proofcheck.py`: checks each proof step for m = 3..10:
  - Step 2 identity at random points;
  - a = u/(1+u)²;
  - the s² formula;
  - T(u) = s·S(a) and the expansion 8N = q² − 3qs + 3s² − T, against direct O(q²) counts for q ≤ 256.

  Log: `logs/design3_proofcheck.log`. (A first draft of Step 2 carried two spurious "+e" terms, which cancelled in the end formula; the pointwise check caught this and the identity above is the corrected one.)

## 5. Prior-art and registry screen (bounded; see `outputs/registry-screen.json`)

- Source (only version v1) leaves it as Conjecture 1. Its companion Conjecture 2 (MathDB 336566) is treated separately and is routine (see the ledger).
- Tang, arXiv:1904.04071 v2 (2019), cites Liu–Ding [15] and gives the general GA₁ 3-design criterion (Lemma 7, Theorems 8–10). Its Theorem 10 needs f̂_B(µ) = Σ(−1)^{Tr(x^t + µ^d x)}, but B₂ has f̂_{B₂}(µ) = f̂_E(µ + 1), a shift, so it does not apply. Tang proves 3-designs only for other blocks (Kasami-APN images, Theorem 13; APN differences, Theorem 16). Body read; Liu–Ding Conjecture 1 is not mentioned as settled.
- Ding–Tang, arXiv:1903.07375 (2019), treats o-polynomial image blocks (Theorem 25, Corollary 29), not trace blocks. Theorem list and conjectures read.
- Xiang–Ling–Wang, arXiv:1907.06235 (2019), treats image sets of quadratic functions (2-designs) and confirms Ding–Tang's Conjecture 3. It does not address this block. Abstract, theorem list and conclusion read.
- Web searches (three standard or extended queries, 2026-11-04) found no resolution of Liu–Ding Conjecture 1.
- Lean Pool HEAD 01db1d70 (unchanged): no design-theory project for this statement. The one generic hit is the M12/M22 Witt-design decide project.
- GitHub repository search (8 queries before a 403 stopped the route, not retried): only a generic design-theory library (ericwang2004/combinatorial-designs-formalization).
- Omega HEAD 6974dba0: complete D5 and Problems trees, no design or Liu–Ding paths. OpenAI/math HEAD 4eaee875 (unchanged; cached preprint listing): no design entries.
- **Limits:** no access to Ding's book *Designs from Linear Codes* (2nd ed., 2022), to later Ding/Tang/Xiang journal versions, or to 2020–2026 papers on GA₁(q) orbit designs beyond the searches above. A published proof of exactly this block could exist; root should run a further literature check (for example Google Scholar "cited by" for arXiv:1707.02003).

## 6. Credit-risk assessment (honest)

- **Odd m is routine.** The block indicator Tr(x³+x) is a weight-(2^{m−1} ± 2^{(m−1)/2}) codeword of the extended dual double-error BCH code. By source Theorem 20 its orbit has q(q−1)/2 members, which equals Kasami's count of codewords of that weight. So the orbit is the full weight class, and Assmus–Mattson (dual distance 6, three nonzero non-full weights) gives 3-designs. Odd m therefore follows from classical results plus the source's stabiliser: a bridge, with zero standalone credit.
- **The substantive case is m ≡ 2 (mod 4)** (m = 6, 10, 14, ...). There the code has five weights, Assmus–Mattson gives only 2-designs, and the orbit (size q(q−1)/2) is a proper subset of the weight-2^{m−1} class ((q−1)(q/2+2) codewords). The proof uses the vanishing s = 0 (the source's own Lemma 18 value) and the new triple-correlation identity of Step 2.
- **Risk of a "routine" or "one-paragraph bridge" ruling (r94 or 374241 precedents): moderate to high.** The argument is about one page of elementary quadratic-form algebra once Tang's criterion (or the three-line Step 0) is in hand. In its favour: experts who explicitly targeted GA₁ 3-designs from this exact paper (Tang 2019) left it open, and the proof covers the full scope of a published conjecture.
- **Significance: modest.** It settles an infinite family of 3-designs conjectured in 2017.
- **Lean cost: MEDIUM-HIGH**, not a finite certificate. It needs GaloisField 2 m for general m, trace properties (additivity, Frobenius invariance, nondegeneracy), a ±1 character sum, cubing bijectivity for odd m, and the GF(4) ⊆ GF(2^m) trace computation for m ≡ 2 (mod 4). Estimated 600–1500 lines; every ingredient exists in Mathlib in some form (`GaloisField.card`, `FiniteField.trace_to_zmod_nondegenerate`, `Algebra.trace` transitivity, Frobenius).

## 7. Statement-correspondence plan for Lean

- Points: `P := (Finset.univ : Finset (GaloisField 2 m))`.
- Tr: `Algebra.trace (ZMod 2) (GaloisField 2 m)`.
- Base block: `B₂ := univ.filter (fun u => Tr (u^3 - u) = 1)`, the literal u³ − u, not the char-2 rewrite.
- Blocks: `𝓑₂ := ((univ ×ˢ univ).filter (·.1 ≠ 0)).image (fun p => B₂.image (fun x => p.1 * x + p.2))`. This is literally GA₁(q)(B₂) as a set of blocks (no multiplicity), matching the source's 𝓑 = GA₁(q)(B).
- t-design (source §1): "𝓑 is a set of k-subsets of P and every t-subset of P is contained in exactly λ blocks". Encode as `IsTDesign t P 𝓑 := (∃ k, ∀ C ∈ 𝓑, C ⊆ P ∧ C.card = k) ∧ ∃ λ, ∀ T ⊆ P, T.card = t → (𝓑.filter (T ⊆ ·)).card = λ`.
- Endpoint: `theorem liuDing_conjecture1 : ∀ m, 3 ≤ m → m % 4 ≠ 0 → IsTDesign 3 univ (𝓑₂ m)`. This states the conjecture literally and is a full-scope proof, not a refutation.
- Bridges to formalize: Step 0 (fibre counting for the block map, the change of variables, which is only bijection bookkeeping) and Steps 1–4. No surrogate predicate is involved: N(u) is an internal lemma, and the endpoint mentions only the literal design.

The draft `lean/LiuDing3Design.lean` (**UNCOMPILED**) contains these definitions, the endpoint, and the lemma decomposition. Lemma bodies marked `sorry` are explicit open proof obligations for the root/Sol formalization stage. It is not a certificate.
