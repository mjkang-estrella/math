# MathDB 358158: the TC-dominant generating set is not optimal for m = 5

Status: candidate refutation with a full Lean endpoint. It has not been independently reviewed and has not been accepted by root. Credit is zero unless root accepts.

## 1. Exact source statement

Source: Hui Chu, Chen Wang and Yiwei Zhang, "Improved constructions of secondary structure avoidance codes for DNA sequences", arXiv:2304.11403v1 (22 Apr 2023). This is the only arXiv version (abs page fetched 2026-11-02, receipt `sources/arxiv-2304.11403-abs.html.receipt.json`). PDF sha256: `8fb7b64fa8fabcb8ad8783575462d28bce329e3c6de37e30fe329da2dc3d3c3f`.

Section V, page 4:

> Conjecture 1. When m is odd, the generating set S with all TC-dominant length-m sequences results in m-SSA codes with the largest rate.

The source definitions used below are as follows.

- Alphabet: D = {A, T, C, G}, with Watson–Crick complement T↔A and C↔G.
- Reverse complement: x_{i+t} = comp(x_{j+m-1-t}) (Section II).
- Definition 4: S_m is the family of maximal sets S ⊆ D^m that contain no two reverse-complement sequences x and y, not necessarily distinct.
- Definition 5: C_n(S) is the set of x ∈ D^n such that every consecutive length-m subsequence of x lies in S.
- Theorem 6: the capacity equals the largest capacity of C_n(S) over S ∈ S_m. The rate of a generating set S is lim (1/n) log2 |C_n(S)|, computed as log2 of the spectral radius of the de Bruijn subgraph on S.
- Definition 3 and Section V: S is TC-dominant when the number of T and C in the word is larger than m/2.

For m = 3 the source checked optimality by brute force. Its Table I gives a rate of 1.6980 bits/nt for the TC-dominant set at m = 5 (Theorem 5: 1 + log2 1.6222).

MathDB record 358158 (chunk `mathdb-normalized-chunk-0009.jsonl`, line 2429): raw sha256 `b0901163a56e0b17244bb034d9f9d079da47e01497a3e69b95f544762c8b76a4`, statement sha256 `9f24a8b5338de2b7bce3883a7a99ee103633099302c72bb2127669695a0c3b3b`. The MathDB paraphrase matches the source.

## 2. Result

**Theorem.** Let m = 5. Let S5 be the TC-dominant generating set with the following 22 words removed, each replaced by its reverse complement:

`AACCC CAACC CAACT CAATC CAATT CAGCC CAGCT CCAAC CCAAT CCAGC CCCAA CCGAC CGACC CGACT CTAAC TAACC TAACT TCAAC TCAAT TCAGC TCGAC TTAAC`

Then S5 ∈ S_5, and

|C_n(S5)| ≥ c1 · (1299/400)^n and |C_n(TC)| ≤ c2 · (649/200)^n

for all n ≥ 5, with constants c1, c2 > 0. Hence rate(S5) ≥ log2 3.2475 = 1.69933... > log2 3.245 = 1.69821... ≥ rate(TC). Conjecture 1 is therefore false for m = 5. This holds whether the rate is read as a limit, a lim sup or a lim inf.

Numerically, ρ(S5) = 3.2480375901 (rate 1.699591 bits/nt), against ρ(TC) = 3.2443334586 (rate 1.697922 bits/nt).

Notes on the certified set:

- The set certified in Lean (`outputs/ssa5-best-set.txt`, sha256 `78dddbd8…`) is the image of the S5 above under the letter swap A↔T. That swap commutes with reverse complementation and preserves the de Bruijn structure. The certified set is therefore "AC-dominant except 22 swaps", and the 22 deviating words are listed in `outputs/ssa5-structure.json`.
- The same optimum value 3.2480375901 was reached by three independent annealing runs (seeds 22, 31 and 41).

## 3. Proof

The proof has four steps.

1. **S5 is a generating set.** Every word w of length 5 satisfies w ≠ rc(w), because m is odd and the middle letter would have to equal its own complement. Exactly one of w and rc(w) lies in S5. This was checked over all 1024 words. Hence S5 contains no reverse-complement pair, and it is maximal: adding any z ∉ S5 adds z together with rc(z) ∈ S5. The same check shows that the TC-dominant set also lies in S_5.

2. **Transfer identity.** For n ≥ 5 and a sequence x of length n+1, x ∈ C_{n+1}(S) holds exactly when init(x) ∈ C_n(S) and the last window of x lies in S. Moreover, the last window of x is the shift of the last window of init(x) by the new letter. For any weight g on words this gives

   Σ_{x ∈ C_{n+1}(S)} g(lw x) = Σ_{y ∈ C_n(S)} Σ_{c : shift(lw y, c) ∈ S} g(shift(lw y, c)).

3. **Collatz–Wielandt certificates.** These use integer vectors from `outputs/ssa5-certificate.json`.
   - Lower bound: v ≥ 0 on S5 satisfies 1299 · v(w) ≤ 400 · Σ_{c: shift(w,c) ∈ S5} v(shift(w,c)) for every w ∈ S5. Then Ψ(n) = Σ_{x ∈ C_n(S5)} v(lw x) satisfies Ψ(n+1) ≥ (1299/400) Ψ(n). We also have Ψ(5) ≥ v(TTACA) = 10^6 and |C_n(S5)| ≥ Ψ(n)/max v.
   - Upper bound: u > 0 on TC satisfies 200 · Σ_{c: shift(w,c) ∈ TC} u(shift(w,c)) ≤ 649 · u(w). Then Φ(n) = Σ_{x ∈ C_n(TC)} u(lw x) satisfies Φ(n+1) ≤ (649/200) Φ(n). We also have Φ(5) ≤ 1024 · max u and |C_n(TC)| ≤ Φ(n)/min u.

4. **Rates.** Taking log2 and dividing by n gives rate_n(S5) − rate_n(TC) ≥ log2(3.2475/3.245) − O(1/n). This yields an ε > 0 with rate_n(TC) + ε ≤ rate_n(S5) for all large n. The limsup, liminf and limit forms follow.

Independent numerical cross-checks:

- `scripts/ssa/count.py` runs a literal brute-force count for n ≤ 8 and agrees with the DP. The DP shows |C_n(S5)| > |C_n(TC)| for every n from 6 to 800.
- numpy eigenvalues give ρ(S5) = 3.24804 and ρ(TC) = 3.24433, matching the source's 1.6222 · 2.

## 4. Lean packet (`formal/SSA5/`)

The modules are Defs, Data (generated), Checks, Bridge, Main, Endpoint and Audit.

- **Pinned toolchain:** Lean 4.34.1 (`dlp-research/.tools/lean-4.34.1-linux`) and the mathlib cache pinned at `d13f23b7…`, used read-only.
- **Literal definitions** (`Defs.lean`): `Base`, `Base.comp`, `rc`, `IsGeneratingSet` (Definition 4, with maximality stated as "every superset with the property equals S"), `tcCount`, `TCDominant m = {x | (m:ℚ)/2 < tcCount x}`, `window`, `code m n S = C_n(S)` and `rateSeq m S n = log2 |C_n(S)| / n`.
- **Endpoints** (`Endpoint.lean`):
  - `conjecture1_false_limsup`: ¬ ∀ m odd, ∀ S generating, limsup rate(S) ≤ limsup rate(TC_m).
  - `conjecture1_false_liminf`: the same statement with liminf.
  - `rate_limit_gap`: there is ε > 0 such that, whenever both limits exist, rate(TC) + ε ≤ rate(S5).
  - `conjecture1_false_m5`: S5 and TC_5 are both generating sets, the strict limsup and liminf gaps hold, and the eventual uniform gap holds.
- **Finite facts:** checked by `decide +kernel` over the 1024 words. No native evaluation is used.
- **Fresh extracted replay** (`replay/`): source hashes are in `replay/source-sha256.txt`. All seven modules rebuilt strictly with `-DwarningAsError=true` and passed `leanchecker` with exit code 0. Logs are in `logs/replay-*`.
- **Axiom audit:** `#print axioms` on every endpoint gives exactly [propext, Classical.choice, Quot.sound]. The `run_cmd` audit covered all 198 declarations in the SSA5 modules, including auto-generated ones, and found 0 disallowed axioms. A token scan found no sorry, admit, axiom, unsafe, native_decide, ofReduceBool, implemented_by or extern.
- **Trust limits:**
  - The mathlib oleans come from the shared cache and were not rebuilt from source.
  - `leanchecker` uses the same Lean kernel, so it is not an independent foundation.
  - The RSS watchdog samples the process; it is not a cgroup limit.

## 5. Prior art, significance and limitations

**Source-internal checks.**

- The source proves nothing that bears on m = 5 optimality. Its Theorem 3 gives the SSA property and Theorem 5 gives the TC rate. Nothing in the source contradicts the conjecture, so this is not a printed-statement correction.
- The source's m = 4 discussion picks "0110 over 1001" patterns by hand. That is the same mechanism as here, but it is used only for even m, and the source still states Conjecture 1 for odd m.
- The 22 swaps exchange TC-weight-3 words of binary patterns 00111, 10011, 11001 and 11100 for their weight-2 partners. This is a new choice that the source does not print.

**Cited papers.** Nguyen et al., arXiv:2302.13714, gives rates for m = 3 only (1.3031 bits/nt), below the source. Benerjee–Banerjee gives 1.1609 for m = 3.

**Follow-up literature.**

- C. Wang, H. Chu, G. Ge and Y. Zhang, "The Capacity of Secondary Structure Avoidance Codes for DNA Sequences", IEEE Trans. Mol. Biol. Multi-Scale Commun. (2024), document 10517954. Its abstract (via the StorageNewsletter press release, 2024-07-08) reports optimal rates only for m = 2 and 3, and mentions generating-set analysis.
- The **journal body is unread**. IEEE returned HTTP 202 with an empty body (a bot challenge), which was not retried. This is a material open point for root: the journal version may restate, drop or already refute Conjecture 1 at m = 5.
- Web searches on 2026-11-02 found no published m = 5 rate above 1.6980.

**Registries.** Live screens at OpenAI/math HEAD 4eaee875 (unchanged) and Omega HEAD 3e6639b6 (2026-11-02, newer than the root-known a9de93a5) found no SSA, DNA or secondary-structure path in the D5, Problems or preprints trees. See `sources/omega-*-tree.json` and `sources/openai-preprints-tree.json`.

**Significance caveats for root.**

- The improvement is small: 0.00167 bits/nt.
- The conjecture comes from an arXiv cs.IT preprint and rested on brute force at m = 3 only.
- The failure is at the first open odd case, and the conjecture is stated for all odd m.
- m = 7 was not improved within the capped searches (`logs/ssa7-*`), so whether TC-dominance fails for every odd m ≥ 5 remains open.
- This is not an automatically generated conjecture.
