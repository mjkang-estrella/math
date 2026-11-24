# R021 manuscript audit, round 1 — *Exact discrete logarithms from a flagged polygonal transform*

2026-10-13. Auditor: Claude Opus 5.5 (`claude-opus-5-5`), acting as a review sub-agent at the user's explicit request. This is an AI audit, not human peer review.

The pinned OpenAI corpus `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` is stipulated true **only in its theorem statements**. The research pin is `mjkang-estrella/math@d513e308d86a38004d78bab9b9e88532e92bf56c`. I read the actual manuscript line by line, and every deduction below was re-derived from it, not from the source proof or the earlier audit.

## Audited artifacts

| Artifact | SHA256 |
| --- | --- |
| `main.tex` (401 lines) | `3d84d154bf87d14ae40177a5ca2536f1ef3928ac80087c1caba697bb7270ef6e` |
| `tmp/main.pdf` (6 pp.) | `72e2bc0b7971edab3eac73ede36430e67c268c7e8c0b1835a14151af2ca3b05d` |

- **PDF build.** The PDF was made by xdvipdfmx at 2026-10-13 11:58:08, the same minute as the last write to `main.tex`. `tmp/main.log` has no errors, warnings, undefined references, or overfull boxes.
- **PDF matches source.** I could not rebuild the PDF because no TeX engine is on PATH here. Instead I compared the full `pdftotext` output against `main.tex` paragraph by paragraph, and they agree. I also checked the rendered pages visually at 80 dpi (`tmp/audit-rebuild/pg-*.png`); all displays typeset correctly.

## Verdict

**REPAIR. The edits are small and non-blocking; no BLOCK.**

- **The mathematics is correct** once required fix M1 is made. M1 is a one-clause range test that the final correction needs in order to equal exactly 1/4.
- **Both source-audit repairs are confirmed.**
- **Two further required fixes**, M2 and M3, concern attribution and bibliography only.

## Confirmation of the source-audit repairs

**Source R1: transform parameter.** Repaired.

- `main.tex:112` sets n = max{128, ⌊log₂p⌋+1} and Q = 2^{16n}. This is exactly the upstream eq. (parameters-n) with N = p, and Q = B^16 = 2^{16n} as in upstream `03-order-transform.tex:37–39`. The manuscript's Q is therefore literally the Q of upstream Lemma 3.2 (`lem:transform`).
- Assumption 1.1(1) (`main.tex:70`) states only this choice, and `main.tex:82` says so ("we use exactly its stated choice").
- b = ⌈log₂q⌉ and B = 2^b now appear only in the label coins: τ, J, the guess widths, L, and the bound q−1 ≥ B/2. Q never depends on b.
- I checked every later use of Q:
  - the bin decoder, which needs q < Q;
  - (3.2), which needs Q ≥ 216q and M ≥ 2;
  - the cell bounds, which need 4 | Q;
  - the Q⁸ denominator of p_j.

  All of them hold for this Q, because q ≤ p−1 < 2^n gives Q/q > 2^{15n} ≥ 2^{1920}. The manuscript does not write this one-line justification; see recommended edit E1.

**Source R2: Cai–Young.** Repaired.

- `main.tex:52–55` and bib entry [3] cite arXiv:2412.17269. I checked the cited abstract and the p. 13 footnote in the local copy (`tmp/ext-caiyoung/cy.pdf`, SHA256 `50566598…c370`).
- The paper models random noise on the controlled-R_k gates of Shor's DLog QFT and its variants. The footnote notes that Mosca–Zalka exactness "assumes exactly precise quantum gates".
- The manuscript's three statements are accurate and adequate:
  - the gate model is "ideal and noiseless";
  - the Cai–Young result is "not a lower bound for every circuit family";
  - "we make no claim of robustness to gate noise".
- Author names, title, arXiv number and year are correct.

## Line-by-line audit of the manuscript's deductions

### §1 (lines 43–103)

- **Phase function.** Eq. (1.1) for g₀ equals upstream eq. (linear-phase): (1−t)(−i)^s + t(−i)^{s+1} = (−i)^s[1+(−i−1)t]. This was checked algebraically and also exactly on grids Q = 16, 64, 1024.
- **Gate set.** The gate set equals upstream `02-model.tex:10–15` and the gate set in upstream `thm:main`.
- **Assumption 1.1(2).** This is upstream `thm:main`: complete prime factorization of every N ≥ 2, with probability one, by a polynomial-time uniform family with polynomial gate and qubit counts. It is applied in §6 to N = p−1. The case p = 2 forces g = 1 and returns early. The hypotheses match.
- **Assumption 1.1(1).** See M3. The upstream statement (`03-order-transform.tex:56–65`) reads: "There is a circuit of size polynomial in b on a b-qubit data register and ancillary registers initially in the all-zero state, with a designated ancillary success outcome, such that its unnormalized matrix on that outcome is A_{k,x} = Q^{-1/2}g(kx/Q). The circuit uses only the fixed finite gate set."
  - Its parameters match.
  - The words "uniform" and "On success no other unobserved register retains information about x" are not in the statement. They are properties of the explicit construction in its proof (`:67–129`): Hadamard and S/Z preparation, O(b²) controlled constant shifts with scratch uncomputed, and an all-zero success test. I re-checked that construction, and the earlier audit simulated it exactly.
  - The theorem is stated "Under Assumption 1.1", so the logic is sound. The defect is that `main.tex:68` attributes the extra content to [5].
- **Barvinok–Pommersheim.** The citation is to [BP, Theorem 4.4 and Algorithm 5.2]; I re-read the local copy (`tmp/ext-barvinok/bp.pdf`, SHA256 `bd803c27…465d`) at text lines 936–1100.
  - Theorem 4.4 applies to any rational polyhedron {⟨cᵢ,x⟩ ≤ βᵢ} with cᵢ ∈ Z^d. It does not require full dimension, so equality constraints written as two inequalities are covered.
  - Algorithm 5.2 counts |P ∩ Z^d| deterministically: the vector l is chosen from the moment curve, and the count is the residue formula (5.2.1).
  - The complexity is L^{O(d)}.
  - The manuscript's paraphrase is accurate.

### §2 trial (lines 105–138)

- **State and transform.** State (2.1) is prepared by Hadamards on 2·16n qubits and reversible modular powering with cleared scratch. Applying the flagged operator to each input register gives an unnormalized success component Σ_{k,l}|k,l⟩⊗v_{k,l}, with v_{k,l} as in §3, because h = g^a. The two flags act on disjoint ancillas and their projectors commute.
- **Decoder.** I re-derived it:
  - For a genuine bin, |kq/Q − j| ≤ q/(2Q) < 1/2. Rounding therefore recovers j uniquely, and tie cases can never pass the equality test.
  - k_q(q−1) < Q.
  - Distinct j give distinct bins.
  - Exact enumeration of every k ∈ [0,Q) for q ≤ 13 confirms that exactly the q bins decode.
- **Event (2.2).** Verification over a′ ∈ [0,q) with ord g = q forces a′ = a, so j′ = aj mod q, which is nonzero because a ≠ 0. Event (2.2) is therefore exact.
- **Edge cases.** q = 2 and h = 1 are handled separately; the remaining case q ≥ 3 is odd. Correct.

### §3 lower bound (lines 140–208)

- **Fourier series.** I re-derived it. T has coefficient (1/4)sinc²(πm/4), and the translate sum is Σ_s i^{(m−1)s} = 4·[m ≡ 1 (4)]. For odd m, sin²(πm/4) = 1/2, so c_m = 8/(π²m²). The sum over m ≡ 1 (4) runs over all odd |m| once, so Σc_m = (8/π²)(π²/8) = 1.
- **Expansion of S.** S = Σc_m D_Q((m−1)t/q + mη/Q) is correct, since mk/Q = mt/q + mη/Q.
- **Main term.** |D_Q(η/Q)| = |sin πη|/|sin(πη/Q)| ≥ 2Q/π for |η| ≤ 1/2, which gives 16Q/π³ ≈ 0.516Q.
- **Aliases.** q is odd, so q | m−1 together with 4 | m−1 forces m = 1 + 4qz. Then |1 + 4qz| ≥ 4q|z| − 1 ≥ 3q|z|, and the coefficient sum is (8/π²)(π²/3)/(9q²) = 8/(27q²) ≤ 8/243 < 1/24.
- **Nonaliases with |m| ≤ M.**
  - Because q ∤ (m−1)t, the point (m−1)t/q has distance at least 1/q from Z.
  - The shift satisfies |mη/Q| ≤ 1/(4q), so the total distance is at least 3/(4q).
  - Since |sin πv| ≥ 2 dist(v,Z), this gives |D_Q| ≤ 2q/3.
  - The two intermediate steps are left implicit in the manuscript (E2).
- **Tail.** c_m ≤ m^{−2}. Then Σ_{n>⌊M⌋} n^{−2} ≤ 1/⌊M⌋ ≤ 2/M, because ⌊M⌋ ≥ M/2 when M ≥ 1. This gives 4/M times Q, i.e. 8q. The factor 2 for ±n is loose, since only one sign is ≡ 1 (4), but harmless.
- **Total.** Q/2 − Q/24 − 2q/3 − 8q ≥ Q/2 − Q/24 − 9q ≥ 5Q/12, which holds iff Q ≥ 216q.
- **Overlap.** The group elements g^z (0 ≤ z < q) are distinct and χ_j is a unit vector. ⟨χ_j, v⟩ = q^{−1/2}Q^{−2}Σ g₀g₀e^{2πij(x+ay)/q} = S(k,j)S(l, aj mod q)/(Q²√q). By Cauchy–Schwarz, p_j ≥ (1/3)⁴/q = 1/(81q). Correct.
- **Exact check.** At Q = 1024 and 2048, min 81q·p_j is 16.34, 11.47 and 9.61 for q = 3, 5, 7 (required ≥ 1).

### §4 exact count (lines 210–260)

- **Collision sum.** (4.1) is ‖v‖² written as a collision sum. The bound |x+ay−x′−ay′| ≤ (1+a)(Q−1) ≤ q(Q−1) gives |z| ≤ Q−1.
- **Cells.** (4.2) is ⌊4cv/Q⌋ = 4n_v + σ_v. Because 4cv and Q·N are integers, the strict inequality 4cv < Q(N+1) becomes the non-strict ... ≤ Q(N+1) − 1.
  - n_v ≤ Q − 1.
  - Period one gives the stated cell formula.
  - Each original tuple has exactly one cell.
- **Weight.** It is the product of four affine factors in (v, n_v), two of them conjugated, so its degree is ≤ 4 and its denominator divides Q⁴. The eight weighted variables are ≥ 0.
- **Stirling expansion.**
  - v^d = Σ S(d,s)·s!·C(v,s) holds for integers v ≥ 0.
  - A product of binomials counts tuples of independent chains, so a monomial ∏v_i^{d_i} adds Σs_i ≤ 4 variables. The dimension is therefore ≤ 13.
  - The number of counts is bounded independently of the input: 4⁴ residue choices × ≤ C(12,4) monomials × Stirling terms.
  - Each count costs L^{O(13)} with L = O(n).
- **Denominator.** p_j ∈ Q^{−8}Z[i] ∩ R = Q^{−8}Z, with 0 ≤ N_j ≤ Q⁸. Correct.
- **Exact check.** At Q = 1024 and 2048 every computed p_j·Q⁸ is an integer.

### §5 completion and amplification (lines 262–345)

**Per-label completion.**
- τ = 1/(256·2^b) ≤ 1/(256q) < 1/(162q) ≤ p_j/2.
- Downward rounding gives 0 ≤ C_j ≤ 1 and 0 ≤ e_j < p_j·2^{−J−1}.
- The guess retention is 2^{2b+1}e_j < p_j/16.
- Per label j the mass is (1/2)p_jC_j + (1/2)·2^{−2b}·2^{2b+1}e_j = τ.
- Exactly q−1 guessed pairs (j, a) pass, because the guess branch tests both 1 ≤ j < q and 0 ≤ a′ < q.
- So P₀ = (q−1)τ, and q > B/2 gives P₀ ≥ 1/512.
- **Edge cases.** "Odd" in "odd q implies q−1 ≥ B/2" is unnecessary but harmless. No division occurs before verification, and dummy denominators are used.
- **Exact check.** For q = 3, 5, 7 and every a, the exact Fraction sums equal (q−1)τ.

**Repetition.** (1−1/512)^{512} ≤ (1+1/512)^{−512} ≤ 1/2, so P ≥ 3/4. P is dyadic with 1024(b+8) denominator bits. Every copy uses fresh registers and has success probability exactly P₀, by the fresh-register consequence of upstream `02-model.tex:37`.

**Quarter correction (lines 302–316).**
- 1/(2P) ≤ 2/3 gives 0 ≤ C ≤ 1, and 0 ≤ e < P·2^{−J*−1}, so 2^{L+1}e < P/4. These match upstream Lemma 6.3 (`lem:quarter`).
- **However, see M1.** Lines 310–312 guess a uniform L-bit integer and "verify it". If verification means only g^{a′} = h, then because 2^L < 2q the integer a + q also verifies whenever a < 2^L − q. The mass then becomes PC/2 + 2e ≠ 1/4.
  - Example: q = 5, L = 3, a ∈ {1, 2}. The mass is 0.256739…, computed exactly by `tmp/checks/manuscript_r1_checks.py`.
  - The words "the unique correct guess" show the intent, but the test is not stated. Lines 280–281 state the range test for the per-label guess, but lines 310–312 omit it.

**Retained records and reflection.**
- The retained-record paragraph matches upstream Lemma 2.2 (`lem:records`): history copies, no copy before interference, clocked controller, address enumeration, inverse.
- The reflection identity holds: ⟨ψ, ψ − 2Πψ⟩ = 1/2, so (2|ψ⟩⟨ψ| − I)(ψ − 2Πψ) = 2Πψ. This is the same identity as upstream eq. (one-reflection).
- Runtime-dependent b (in §6, q = ℓ is computed during the run) is covered by the address-enumeration sentence. Q is fixed by p.

### §6 arbitrary order (lines 347–371)

- **Order computation.** Order stripping keeps the invariant ord | m and terminates with ord = m. The number of tests is O(log p).
- **Prime-power digits.**
  - g_ℓ has order exactly ℓ^e, and γ has order ℓ.
  - If x_k ≡ A (mod ℓ^k), where A is the logarithm, then (h_ℓ g_ℓ^{−x_k})^{ℓ^{e−1−k}} = g_ℓ^{(A−x_k)ℓ^{e−1−k}} = γ^{(A−x_k)/ℓ^k}. So d_k ≡ (A−x_k)/ℓ^k (mod ℓ) and the invariant advances.
  - CRT then gives the unique A ∈ [0, m).
- **Calls.** There are Σe ≤ log₂m calls. Each call's target lies in ⟨γ⟩ by the computation above, so the prime-order promise holds. Targets equal to 1 and ℓ = 2 fall to direct testing.
- **Certainty.** Each earlier output is certain, so its output register is a basis state in product with its retained history. That makes it valid classical control.
- **Credit.** The reduction is correctly credited as classical (Pohlig–Hellman style), with no novelty claimed.

### Claim scope, abstract, contribution boundary

- **Abstract.** Every abstract sentence is supported by the body.
- **Credit and priority.** The paper credits [5] for the transform, completion and amplification, and states that exact DLog algorithms (Mosca–Zalka) predate it. It does not claim priority.
- **Duplicate scan.** I scanned the names of all 749 pinned preprint directories for logarithm, Fourier and Shor terms. None is a discrete-logarithm paper. The nearest ones, *Finite tensor savings and exact Fourier circuits* and *An explicit power saving for the exact DFT*, concern classical arithmetic circuits.
- **Imran–Ivanyos.** The staged I324 literature record (`sources/i324_exact_discrete_logarithm_contribution/literature.md`, SHA256 `eb4cfad4…c368`) gives their fixed-basis consequence only for group orders with constant-bounded prime factors. The manuscript's claim does not conflict with it. Citing it would sharpen the boundary (E5). I did not re-read Imran–Ivanyos.

### References

- [2] BHMT, [3] Cai–Young and [4] Mosca–Zalka are correct; I cross-checked them against the upstream bibliography and the Cai–Young reference list.
- [5] has the correct title, date, revision and URL path.
- [1] has the wrong volume title (M2). The official MSRI contents page for Volume 38 reads "New Perspectives in **Algebraic** Combinatorics, edited by Billera, Björner, Greene, Simion, and Stanley", and lists Barvinok–Pommersheim at pp. 91–147. My copy is `tmp/ext-msri/b38.html`, SHA256 `a0b9c5ae283f4ad3393e5362a3b77645d7a2a7b88f06fb5739ad0ded5a9a6149`. The chapter PDF's running head says "Geometric", which is evidently where the manuscript's wording came from, but the volume title is "Algebraic".

## Required fixes

**M1 — final correction range test (`main.tex:310–312`).** Replace

> Otherwise guess a uniform $L$-bit logarithm, verify it, and retain the unique correct guess with probability $2^{L+1}e<P/4$.

with

> Otherwise guess a uniform $L$-bit integer $a'$, require $a'<q$ and $g^{a'}=h$, and retain with probability $2^{L+1}e<P/4$. Exactly one guess, $a'=a$, passes these tests.

Without the a′ < q clause, the stated mass identity on line 314 is false whenever a < 2^b − q.

**M2 — bibliography [1] (`main.tex:381`).** Replace "in New Perspectives in Geometric Combinatorics, MSRI Publications 38" with

> in L.~J.~Billera, A.~Bj\"orner, C.~Greene, R.~Simion, and R.~P.~Stanley (eds.), New Perspectives in Algebraic Combinatorics, MSRI Publications 38

**M3 — attribution of Assumption 1.1(1) (`main.tex:68–82`).** The stipulated statement is upstream Lemma 3.2. It asserts a polynomial-size circuit, but neither uniformity nor the ancilla-reset property. In addition, "no other unobserved register retains information about x" reads as false in §2, where the group register does depend on x. Suggested replacement for item (1)'s last sentence and for lines 81–82:

> On the success outcome every ancillary register of this circuit is in a fixed state independent of $x$.

> The first item is [5, Lemma 3.2] with its stated choice $Q=2^{16n}$; uniform generation and the fixed ancillary success state are read off the explicit circuit in its proof (Hadamard preparation, $O(n^2)$ controlled constant shifts with scratch uncomputed, and an all-zero success test). The second item is [5, Theorem 1.1].

## Recommended edits (non-blocking)

- **E1 (line 187, and line 181 "M ≥ 2").** Add: "Since $q\le p-1<2^n$ and $Q=2^{16n}$, we have $Q/q>2^{15n}$; in particular $Q\ge216q$, $M\ge2$ and $q<Q$."
- **E2 (lines 176–179).** Make the missing steps explicit: "...hence distance at least $3/(4q)$ from $\mathbb Z$; since $|\sin\pi v|\ge2\,\mathrm{dist}(v,\mathbb Z)$, $|D_Q(v)|\le2q/3$."
- **E3 (line 345).** "This proves Theorem 1.2 for supplied prime order" is loose, because Theorem 1.2 has no supplied-order input. State a Proposition (supplied prime order q) at the start of §2 and conclude Theorem 1.2 in §6.
- **E4 (lines 334–335).** "The first reflection is V(2|0⟩⟨0|−I)V^{−1}" reads as the first one applied, which is I − 2Π. Write "the reflection 2|ψ⟩⟨ψ|−I equals ...".
- **E5.** Cite theorem numbers where [5] is cited: Lemma 3.2 for the transform, Lemma 2.2 for records (`main.tex:325`), and Lemma 6.3 for the quarter correction (`main.tex:302`). Optionally cite Imran–Ivanyos (QIC 22 (2022) 770–789; arXiv:2304.08376) as the fixed-basis exact line restricted to bounded prime factors.
- **E6.** Delete "odd" at line 294. q > B/2 alone gives q−1 ≥ B/2.

## Supporting checks (package `tmp/` only)

`tmp/checks/manuscript_r1_checks.py` (SHA256 `19ec5f426c8a79f3c72dab46c61ae544ebe8ba570a4e0fc090f97062e8f847bd`) was run with `python3 -I -B`. Its output is in `tmp/checks/manuscript_r1_outputs.txt` (`5411f6b6dee0f8ea2a23f440199980418a70dbd22e81fcd3568b98a87fd20512`). It uses exact Gaussian-rational arithmetic and checks:

- g₀ equals upstream g on three grids.
- The decoder is exact for q ≤ 13.
- For q = 3, 5, 7 and all a, j:
  - p_j ≥ 1/(81q);
  - p_jQ⁸ ∈ Z;
  - the C_j and e_j bounds hold;
  - the per-label completion sums exactly to (q−1)τ;
  - P ≥ 3/4;
  - the quarter identity holds exactly with the M1 range test, and fails (0.256739) without it for q = 5.

These checks use small Q ≥ 216q, not 2^{16n}; the written proof does not depend on Q beyond Q ≥ 216q, M ≥ 2 and 4 | Q. Numerical checks corroborate the proof; they are not the proof.

Other supporting files: `tmp/main-audit.txt` (pdftotext of the audited PDF), `tmp/audit-rebuild/` (a source copy and page renders; the rebuild was not possible), and `tmp/ext-msri/b38.html`. One download briefly went to `/tmp/r021-audit-dl/`. I moved it into the package and removed that directory.

## Not inspected

- The truth of any upstream theorem (stipulated).
- Upstream §§4–5 and the appendix.
- The Barvinok 1994 original.
- The proofs in Cai–Young.
- The bodies of Mosca–Zalka, Imran–Ivanyos and the other I324 literature beyond the staged records.
- Anything beyond bounded duplicate scans; there is no priority guarantee.

I could not recompile the PDF locally. I made no manuscript edits, commits or index edits, spawned no agents, and made no external submissions.
