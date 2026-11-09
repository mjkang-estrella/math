# Lean packet: MathDB 334207 (Ding–Zhang–Ge Conjecture 2)

Candidate only. It is pending independent statement-fidelity, significance and novelty review and root acceptance. No credit is claimed.

## Files

* `formal/BSymbol.lean`: the development (single file, namespace `BSym334207`).
* `fresh-replay/BSymbol.lean`: byte-identical sanitized copy, used for the fresh extracted replay.
* `fresh-replay/Audit.lean`: local-declaration inventory and axiom audit, plus `#print axioms` and `#print` of the statement definitions.
* `334207-proof-source.zip`: archive of the two Lean sources and this README (hash in `SHA256SUMS.json`).
* Runner scripts: `scripts/lean.py`, `scripts/replay_lean.py`, `scripts/checker.py`, `scripts/limited.py`.

Toolchain: Lean 4.34.1 (`/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin`). Mathlib is the cached build at `openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages`, pinned at d13f23b723b8a846827a245b89c10fc7d3f11612 and used read-only via `LEAN_PATH`. Every run used `-j1 -DwarningAsError=true` under `scripts/limited.py`: 2 CPUs, CPU 120 s, wall 140 s, sampled RSS 6 GiB.

## Endpoint theorems

```lean
theorem BSym334207.dzg_conjecture2 (q : ℕ) (hq : IsPrimePow q) (b n : ℕ) (hb : 2 ≤ b) (hn : 2 * b ≤ n) :
    (∃ (K : Type) (_ : Field K), Nat.card K = q) ∧
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = q →
      ∃ C : Submodule K (Fin n → K), IsLinearMDSBSymbol b (2 * b) C

theorem BSym334207.dzg_conjecture2_field {F : Type*} [Field F] [Finite F] (b n : ℕ) (hb : 2 ≤ b) (hn : 2 * b ≤ n) :
    ∃ C : Submodule F (Fin n → F), IsLinearMDSBSymbol b (2 * b) C
```

`#print axioms` for both: `[propext, Classical.choice, Quot.sound]`.

## Statement fidelity: source definition to Lean declaration

The source is arXiv:1609.09236, Section 2 and Conjecture 2. Indices run over ℤ_n = `Fin n`.

| Source | Lean |
|---|---|
| index i + j taken mod n | `cyc i j = ⟨(i + j) % n, _⟩` |
| wt_b(x) = \|{i : (x_i,…,x_{i+b−1}) ≠ 0}\| | `bWeight b x = #{i : Fin n \| ∃ j < b, x (cyc i j) ≠ 0}` |
| D_b(x,y) = \|{i : (x_i,…,x_{i+b−1}) ≠ (y_i,…,y_{i+b−1})}\| | `bDist b x y = #{i \| ∃ j < b, x (cyc i j) ≠ y (cyc i j)}` |
| minimum b-distance d_b of C (min over distinct pairs) | `HasMinBDist b C d`: some distinct pair at distance d, and all distinct pairs at distance ≥ d |
| linear code | `C : Submodule F (Fin n → F)` |
| (n, M, d_b)_q code with M = q^{n−d_b+b}, i.e. MDS (n, d_b)_q | `IsLinearMDSBSymbol b d C := HasMinBDist b C d ∧ Nat.card C = Nat.card F ^ (n - d + b)` |
| "q a prime power", codes over F_q | `IsPrimePow q`; every finite field `K` with `Nat.card K = q`, plus the existence of one such field (`GaloisField p k`) |
| b ≥ 2, n ≥ 2b, d_b = 2b | `2 ≤ b`, `2 * b ≤ n`, `d = 2 * b` |

Notes for reviewers:

* With d = 2b ≤ n, natural subtraction gives n − d + b = n − b exactly.
* The two-pair formulation of the minimum distance is equivalent to "min over distinct pairs = d" whenever |C| ≥ 2. Here the first conjunct exhibits a pair, so it is in fact stronger.
* Field cardinality is `Nat.card`. GaloisField only carries a `Finite` instance in this Mathlib.

## Proof structure (matches `BSYMBOL-ORDINARY-PROOF.md`)

* `sv`, `V`: the recursive 0/1 window sequence. Recursion is on b via (b, n) → (n mod b, b + n mod b).
* `bridge_window`: the bridge lemma. It is proved by a single linear functional ℓ on F^r. ℓ vanishes on a spanning r-window of the smaller sequence, so ℓ = 0, which kills the coefficients.
* `windows_good`: Theorem A, by strong induction on b.
* `parity`, `parity_surj`, `card_ker`: C = ker H has cardinality q^{n−b}, by rank–nullity and `Module.natCard_eq_pow_finrank`.
* `weight_ge`: every nonzero codeword has b-weight ≥ 2b. The proof takes a zero window, rotates, and shows the support has width < b (otherwise 2b distinct nonzero windows exist); window independence then forces c = 0.
* `weight_le`, `V_b_eq_V_zero`: the codeword δ_0 − δ_b lies in C and has b-weight ≤ 2b.
* `dzg_conjecture2_field`, `dzg_conjecture2`: the endpoints.

## Verification receipts

See `verification.json` for the full record:

* Strict build of `formal/BSymbol.lean`: `logs/lean-B7.log` (empty), `logs/lean-B7.receipt.json` (returncode 0).
* Fresh extracted replay: `logs/fresh-bsymbol.*` (olean build, returncode 0), `logs/fresh-kernel.*` (`leanchecker -v BSymbol`, "replaying BSymbol", returncode 0), `logs/fresh-audit.*` (157 local declarations inventoried; none unsafe, none an axiom; every transitive axiom set ⊆ {propext, Classical.choice, Quot.sound}).
* `leanchecker --fresh`: see `verification.json` (attempted within the caps).
* Forbidden-token scan of the source (sorry, admit, axiom, unsafe, native_decide, ofReduceBool, implemented_by, extern): no matches.

Trust limits: the cached upstream Mathlib oleans were not rebuilt from source; there is no source-to-olean attestation. RSS caps are sampled, not cgroup-enforced.
