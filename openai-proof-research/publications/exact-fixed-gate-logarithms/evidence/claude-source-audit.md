# R021 exact fixed-gate discrete logarithms — independent source audit (Claude Opus 5.5)

2026-10-13. Auditor: Claude Opus 5.5 (`claude-opus-5-5`), acting as a review sub-agent at the user's explicit request. This is an AI audit, not human peer review and not a formal proof certificate. The pinned OpenAI corpus at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` is stipulated true. Only its **theorem statements** are taken as stipulated. Where R021 uses a source *proof* outside the stated hypotheses, I re-verified that proof myself.

## Verdict

**PASS with two required REPAIRs (non-blocking) and three recommended edits.** No mathematical step of the prime-order core, the completion, the amplification or the prime-power extension is false. The theorem as stated in R021 §1 holds under the stipulated corpus once repair R1 is made. R1 is a hypothesis-matching defect in how the upstream transform lemma is invoked, and a one-line parameter change fixes it. R2 is a missing-literature boundary that the manuscript must address. Neither changes the theorem.

## Inputs and authentication

Research pin `mjkang-estrella/math@d513e308d86a38004d78bab9b9e88532e92bf56c`, staged under `/tmp/publication-r017-r022/`. All 12 R021/i322–i324 records match `manifest.json` (0 mismatches). I read each of the following in full:

| File | SHA256 |
| --- | --- |
| findings/R021-exact-fixed-gate-discrete-logarithms.md | `b8996f53…60cd` |
| iterations/i322-parent-exactification-bridge.md | `6a059b5d…ebdc` |
| iterations/i322-exact-discrete-logarithm-candidate.md | `0a0a4b9d…a7d` |
| experiments/i323_exact_discrete_logarithm_proof/analysis.md | `040fc4b591c82845a37446d29bd01b1515fa2a759a736b11a8f0ece91f31a59c` |
| reviews/i323-exact-discrete-logarithm-proof.md | `70f67847…f90a` |
| experiments/i324_…/analysis.md, reviews/i324-…md | `4dcea65b…4f341`, `6ee4d9e5…d810` |
| sources/i322, i323, i324 literature.md | `5bbe3bf8…`, `5be881ac…`, `eb4cfad4…` |

I also read the i323 and i324 parent dispositions. Abbreviated hashes are prefixes and suffixes of the full SHA256 values. The full R021 hash is `b8996f534c370f5465d5fa30e3f150a39e32d3a1528b770909d33d4e4b1360cd`; the others equal the values recorded in the I323/I324 dispositions and in `manifest.json`.

I independently fetched the pinned upstream source, *Exact quantum factoring over a fixed finite gate set (Sept 25 2026)*, from `raw.githubusercontent.com/openai/math/fd4aeeb2…/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/build/`:

- `sections/01-introduction.tex` `6d001bb6…7cc`. Read all 129 lines; `thm:main` is at lines 10–12.
- `sections/02-model.tex` `4cb63e05…3ac`. Read all 39 lines: gate set (l.10–15), `lem:dyadic` (l.19–24), retention convention (l.26), `lem:records` (l.28–35), fresh-register consequence (l.37).
- `sections/03-order-transform.tex` `b9e0f918…f31`. Read all 227 lines; `lem:transform` is at l.56–130.
- `sections/06-exactness.tex` `e80b0ef8…25a`. Read all 137 lines: `lem:completion`, `prop:known-probability`, `lem:quarter`, and the final reflection proof.
- Fetched but not semantically audited (only grepped for DLog content; none found):
  - `04-dyadic-order.tex` `c3561cc4…`
  - `05-factor-process.tex` `0e442c01…`
  - `appendix-primality.tex` `56f34d05…`
  - `bibliography.tex` `60944d66…`
  - `main.tex` `a38f067a…`

Hashes for sections 01, 02, 03 and 06 match the I323 ledger.

Raw bodies are kept in `tmp/upstream/` (gitignored). Three extra files, `upstream/sections-0{2,3,6}-*.tex`, appeared in that directory without my writing them. They are byte-identical (same hashes) to the sections above, and I did not use them.

## Hypothesis audit of each stipulated input

1. **`thm:main` (exact factoring).** It covers every N≥2, probability one, a polynomial uniform family, and the gate set {NOT, CNOT, Toffoli, H, S} with inverses and singly controlled versions. R021 §6 applies it to N=p−1≥2 (p=2 forces g=1 and returns early). The hypotheses match.

2. **`lem:transform` — REPAIR R1.** The lemma is stated "on a b-qubit data register" with Q=B^16=2^b, b=16n and n=max{128, ⌊log₂N⌋+1} (03-order-transform.tex l.37–39; 02-model.tex l.5–6). R021 §1 paraphrases it as "for Q a power of two" and §2 uses Q=2^10·B² with B=2^⌈log₂q⌉. That Q is not of the stated form; for example, q=3 gives Q=2^14. The stipulation therefore does not cover it, and R021 depends on the proof rather than the statement. The I323 analysis (§1) notices this ("No step requires the original parameter choice b=16n") but treats it as a reading of the proof.

   - **My verification.** The source proof, lines 67–125, is generic for any b≥2. The χ preparation needs two bits, the overlap identity (eq:phase-overlap) needs 4|Q, and the bit decomposition xk ≡ D+(Q/2)h mod Q holds for every b. I also simulated the exact circuit in the source proof: Hadamard order, controlled shifts T_{2^{i+j}x_i k_j}, physical bit reversal, and success on the all-zero phase register. For b=2,…,6 the unnormalized success matrix equals Q^{-1/2}g(kx/Q) to 2e-16 (`tmp/checks/check_transform.py`). The mathematics is therefore right.
   - **Exact replacement (preferred: stays inside the stated lemma).** Set n' = max{128, ⌈log₂p⌉} and Q = 2^{16n'}. This Q is the lemma's Q for any N with ⌊log₂N⌋+1 = n', for example N = 2^{n'−1}.
     - Every downstream use survives:
       - Q ≥ 2^{16⌈log₂q⌉} ≥ 216q and M = Q/(2q) ≥ 2, so the bound in (S) holds verbatim.
       - q/Q < 1, so bin decoding is unchanged.
       - p_j ≥ 1/(81q) does not depend on Q.
       - The count has O(log Q) = O(n') bit sizes.
       - The denominator of p_j divides Q^8 = 2^{128n'}.
       - τ, J, P_0 and the 1024-fold repetition depend only on b = ⌈log₂q⌉ and are unchanged.
     - Bonus: Q now depends only on the input length. One transform circuit serves every digit call in §6, which simplifies the runtime-b controller paragraph in R021 §5 and I323 §7.
   - **Alternative replacement.** State a lemma "for every b≥2 and Q=2^b" in the manuscript and reproduce the four-line proof (overlap identity plus bit decomposition) as the manuscript's own argument, crediting the source construction.

   Either way, the manuscript must not say the stipulated lemma covers an arbitrary power of two.

3. **`lem:dyadic`.** The hypothesis is a dyadic in [0,1] specified by a polynomial-time computation with polynomial bit length, and every retention in R021 satisfies it. I checked:
   - C_j and e_j are dyadic; p_j = N_j/Q^8.
   - 2^{2b+1}e_j < 1/16.
   - C and 2^{L+1}e in §5a are at most 1/4.
   - Label-dependent denominators are padded, as the lemma's proof allows.

4. **`lem:records` and the fresh-register consequence (l.37).**
   - The prime-order preparation is a polynomially clocked procedure with fixed gates, basis measurements (the flags and k, l) and polynomial classical control (decode, verify, Barvinok count, coins).
   - The group register is never measured. It is "old quantum work", and the consequence on l.37 gives the conditional probabilities.
   - x and y are not copied before the transforms, which matches the lemma's "no label is copied before an intended interference".

   The hypotheses match.

5. **`lem:completion`, `lem:quarter`, final reflection.**
   - R021 does not invoke `lem:completion` literally. Its per-label construction sums over q−1 labels with one guess branch, and it is re-derived in full in R021 §5. I re-derived it and checked it in exact rational arithmetic (below).
   - §5a is `lem:quarter` with the known P, J* = L+2 and the same floor; it matches the source pattern.
   - The reflection identity (2|ψ⟩⟨ψ|−I)(ψ−2G) = 2G at ‖G‖² = 1/4 is the source's eq:one-reflection.

## Audit of the new deductions

**§2 trial and event.** The state after both flagged transforms is Σ_{k,l}|k,l⟩⊗v_{k,l} with v_{k,l} = Q^{-2}Σ g(kx/Q)g(ly/Q)|g^{x+ay}⟩. The two transforms act on disjoint registers, so their success projectors commute. The decoder accepts k iff k = k_q(j) (|kq/Q−j| ≤ q/(2Q) < 1/2). Over [0,q), verification forces a' = a, so the passing event for label j is exactly {k = k_q(j), l = k_q(aj mod q), both flags}. I checked this by exhaustive decoding of every k in [0,Q) for q ≤ 13 at the true Q. **Correct.**

**§3 Fourier lower bound.**
- I re-derived (F): the coefficients are 8/(π²m²) on m ≡ 1 mod 4 (including negative m) under the e^{−2πimt} convention, and 0 otherwise. Exact piecewise integration agrees to 3e-16 for |m| ≤ 41.
- Main term: 16Q/π³ ≈ 0.516Q.
- Aliases: m = 1+4qz because q is odd and prime and t ≢ 0; total ≤ 8/(27q²) ≤ 8/243 < 1/24.
- Nonaliases with |m| ≤ M: distance ≥ 3/(4q), so |D_Q| ≤ 2q/3.
- Tail: ≤ 4/M, contributing 8q.
- Total: |S| ≥ 5Q/12, using Q ≥ 216q.
- The character overlap factorization, including the sign of the conjugated character, gives p_j ≥ |⟨χ_j|v⟩|² ≥ 1/(81q) by Cauchy–Schwarz. χ_j is purely analytical.
- Numerically, at the actual Q, min|S|/Q is 0.670, 0.613, 0.587, 0.562 and 0.555 for q = 3, 5, 7, 11, 13 (required: 0.4167).
- Exactly, min over all a, j of 81q·p_j is 16.3, 11.5, 9.6, 8.1 and 7.7 (required: ≥1). The bound is conservative but valid.

**Correct.**

**§4 exact count.**
- (P) is the squared norm. Group-state equality is equivalent to x+ay−x'−ay' = qz with |z| ≤ Q−1.
- The floor cells Q(4n+σ) ≤ 4cv ≤ Q(4n+σ+1)−1 have exactly one solution, with n < Q.
- The cell phase (−i)^σ[1+(−i−1)u] matches eq:linear-phase.
- I brute-forced every quadruple for (q,Q) ∈ {(3,16), (3,32), (5,32), (7,64)} and all a, j. The cell-encoded sum (P) equals the residue-sum p_j, each cell is unique, and |z| ≤ Q−1 (`check_cells.py`).
- The Stirling/binomial lift v^d = Σ S(d,s)s!·C(v,s), using chains 0 ≤ t_1 < … < t_s < v, is correct. It adds at most 4 coordinates, so the dimension is ≤ 13. No weight involves z.

On the external counting theorem: I fetched Barvinok–Pommersheim, MSRI Publ. 38 (1999), `library.slmath.org/books/Book38/files/barvinok.pdf`, SHA256 `bd803c27…465d` (matches I323), and read Theorem 4.2, Theorem 4.4 with its proof sketch, and Definition 5.1 through eq. (5.2.1).
- Theorem 4.4 applies to any rational polyhedron {⟨c_i,x⟩ ≤ β_i}, c_i ∈ Z^d. Equalities given as two inequalities and lower-dimensional polytopes are covered by the statement.
- Algorithm 5.2 is deterministic: l is chosen from the moment curve, followed by an exact Todd-polynomial evaluation.
- The cost is L^{O(d)}, which is polynomial for d = 13.

Every hypothesis is met. **Correct.**

**§5 per-label dyadic completion.** τ = 2^{−b−8} ≤ 1/(256q) < p_j/2. The bounds 0 ≤ C_j ≤ 1, 0 ≤ e_j < p_j·2^{−J−1} and 2^{2b+1}e_j < 1/16 all hold. Per label, the mass is p_jC_j/2 + e_j = τ. Odd prime q > B/2 gives q−1 ≥ B/2, so P_0 = (q−1)τ ≥ 1/512. With 1024 repetitions, P ≥ 3/4, and §5a gives exactly 1/4.

I checked all of this in exact `Fraction` arithmetic with the actual exact p_j, for every a and j and q ∈ {3,5,7,11,13}. The total per a is exactly (q−1)τ. P is 0.8649, 0.8649, 0.9504, 0.9182 and 0.9504, and the quarter identity is exact.

- **No circularity.** p_j is computed from (q, j, a'), and only after a' passes g^{a'} = h. Rejected branches never divide. The guess branch obtains the same p_j from its own verified pair.
- **No postselection.** Failed flags and failed verifications set success to 0, and their mass is retained (02-model l.26).
- **No expected-time loop.** The repetition count is fixed at 1024 and there is one Grover step.

**Correct.**

**§5a/§6 amplification and full order.** The reflection algebra is as in the source. The order stripping m ← m/ℓ while g^{m/ℓ} = 1 terminates at ord(g). The digit identity (h_ℓ g_ℓ^{−x_k})^{ℓ^{e−1−k}} = γ^{d_k} holds, and CRT recovers a. ℓ = 2, h = 1, g = 1 and p = 2 are all covered. A classical test with a brute-force prime-order oracle recovered both a and ord(g) on 3000 random instances with p < 3000. **Correct.**

**Uniform worst-case implementation.** Every branch is clocked: the Barvinok cost L^{O(13)}, reversible arithmetic, and bounded guesses. R021 §5 and I323 §7 handle runtime-dependent b with controller overhead. This is acceptable, and repair R1's choice Q = 2^{16n'} removes the need. **Recommended edit E2:** state that the polynomial clock for the counting routine exists (fixed algorithm, fixed d) and that its exponent is O(13) in Barvinok's analysis. This makes clear the family is uniform but astronomically large, which R021 already concedes for practicality.

## Literature and contribution boundary

- **The pinned corpus has no duplicate.** I listed all 749 directories under `preprints/` at the pin; no DLog paper is among them. The factoring paper mentions discrete logarithms only when crediting Shor and Mosca–Zalka (01-introduction l.16–33). I checked the closest companion, *Finite tensor savings and exact Fourier circuits* (intro `7d7df83a…`). It concerns classical linear arithmetic circuits for F_n with arbitrary coefficients, not quantum fixed-gate circuits, so it is not a duplicate.
- **Mosca–Zalka, quant-ph/0301093** (v1 only, 17 Jan 2003). I checked the abstract page myself: the exact QFT and DLog circuits are "uniform" only in the sense that the gate parameters can be computed efficiently. Those are input-dependent rotations, which matches I322/I324. I did not re-read the body; for Sections 3–5 I rely on I324's record.
- **REPAIR R2 — missing directly relevant predecessor.** Cai–Young, *Quantum Algorithms for Discrete Log Require Precise Rotations*, arXiv:2412.17269v1 (23 Dec 2024), PDF SHA256 `50566598…c370`. I read the abstract, Section 1 (pp. 2–4), Theorems 2–3 and the footnote on p. 13 about Mosca–Zalka exactness.
  - The theorems show that Shor's DLog algorithm and its QFT-based variants fail when every controlled-R_k gate (k ≥ b) carries Gaussian relative noise above a vanishing level. Their footnote states that the Mosca–Zalka exact algorithm "assumes exactly precise quantum gates".
  - This does **not** contradict R021. The paper is a noise-model failure analysis of QFT-rotation circuits, not a lower bound for all DLog algorithms, and R021 contains no R_k gates. But the title asserts the opposite of what a reader of R021 will infer, and none of the I322–I324 literature records cites it.
  - The manuscript must cite it and state both boundaries:
    1. R021 removes small-angle rotations from the *ideal* gate model.
    2. R021 makes no claim about robustness to gate noise. Its H and S gates are assumed exact, and nothing is proved about noisy or fault-tolerant execution.

  Cite Cai's corresponding factoring-noise paper as well, if the manuscript discusses noise at all.
- **Imran–Ivanyos (2022/2023), Dong et al. 2025, Brassard–Høyer, van Dam, Takahashi–Tani, Ozols–Roetteler–Roland, Lev, Pilatte, Hadfield.** I did not re-read these; I rely on the I324 operation-level comparison and found nothing in my searches that contradicts it. One search snippet confirms that Imran–Ivanyos obtain exact QFT_m via Cleve–Coppersmith for smooth m and via Mosca–Zalka for general m. That is consistent with I324's statement that their fixed-basis consequence needs bounded prime factors.
- **Searches.** Two extended and three standard web searches (exact DLog with a fixed or finite gate set; follow-ups to the exact-factoring paper; exact HSP over growing Z_p without an exact QFT) found no prior or post-September-2026 probability-one fixed-gate DLog algorithm. de Beaudrap, arXiv:1509.07789, came up as a background lead and was not used as evidence. This is bounded search, not a priority proof.
- **Contribution assessment (my own, advisory).** The new content is a genuine but modest extension of the upstream method. It consists of a two-register selected-frequency event with a uniform 1/(81q) bound, plus the observation that the verified witness a linearizes the collision constraint, which brings in fixed-dimensional lattice counting. Upstream used power sums instead. Everything else is credited source machinery. I agree with I324's boundary that this is "one combined theorem" with priority unestablished. **Recommended edit E1:** the manuscript abstract should not describe the transform, completion or amplification as new.

## Required and recommended edits (precise locations)

- **R1 (required).** In R021 §1 ¶3, "for Q a power of two", and in §2, "Q=2^10 B²": replace Q with 2^{16·max(128,⌈log₂p⌉)}, or add a self-contained general-b lemma and proof as described above. Then re-state "Q ≥ 216q and M ≥ 2" as consequences.
- **R2 (required).** In the literature and limits sections (R021 §7 and the manuscript introduction), cite Cai–Young arXiv:2412.17269 and state the ideal-gate and no-noise-claim boundary.
- **E1.** Keep the attribution boundary for the transform, completion and amplification (see above).
- **E2.** State the counting cost L^{O(d)} with d ≤ 13 and its determinism. Cite Barvinok's original paper (Math. Oper. Res. 19 (1994)) as well as the survey; I did not read the 1994 paper.
- **E3.** The manuscript must replace the internal file reference in R021 §5 ("`i322-parent-exactification-bridge.md`") with the self-contained §5a argument, which already suffices because P is known. The witness-dependent generic bridge is not needed for this theorem.

## Not inspected

- Truth of any upstream theorem (stipulated).
- Upstream Sections 4 and 5, the primality appendix and the bibliography body, beyond grepping for DLog content.
- Barvinok 1994 original, and the BP survey outside pp. 106–112.
- The bodies of Mosca–Zalka, Imran–Ivanyos, Dong et al., van Dam, Takahashi–Tani, ORR, Lev, Pilatte and Hadfield.
- Cai–Young proofs (only statements and scope were read).
- Any manuscript draft; the parent is drafting separately and I did not see it.

The numerical checks are corroborating evidence, not proof. The proof verdict rests on the written derivations re-done above.

## Reproduction

Scripts and outputs are in `tmp/checks/` (gitignored), run with `python3 -I`:

| File | SHA256 |
| --- | --- |
| check_transform.py | `21843b06…9108` |
| check_core.py | `2c79e1c2…69c2` |
| check_cells.py | `be7ca653…8f5b` |
| check_misc.py | `7be09629…87d1` |
| outputs.txt | `1b6b27c2…4809` |

External bodies are isolated in `tmp/upstream`, `tmp/upstream-ft`, `tmp/upstream-meta` (pinned README `5e8878ee…`, preprints tree listing), `tmp/ext-barvinok` and `tmp/ext-caiyoung`. Nothing outside this package was written. I made no commits, edited no index, spawned no agents and made no external submissions.
