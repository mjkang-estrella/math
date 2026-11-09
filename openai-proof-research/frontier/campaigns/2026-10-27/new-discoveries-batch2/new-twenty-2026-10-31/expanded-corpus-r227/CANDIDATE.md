# Candidate status — expanded-corpus-r227 (Claude lane)

**No candidate is proposed.** None of the 20 reserved records yielded a new, full-scope exact
solution that survives the campaign's credit rules. Nothing here should be counted.

## Closest calls (recorded so nobody repeats them)

### 364481 — pairwise-product injectivity (Ballantine–Beck–Merca, Conjecture 2)

This lane found a short, complete proof:

- Let φ_λ(t) = Σ λ_i^t.
- If pre₂(λ) = pre₂(μ), then Σ_{i<j}(λ_iλ_j)^t agrees for both partitions. That sum equals ½(φ(t)² − φ(2t)), so

  φ_λ(2t) − φ_μ(2t) = (φ_λ(t) − φ_μ(t)) (φ_λ(t) + φ_μ(t)).
- Equal size n gives a difference of 0 at t = 1, hence at every t = 2^j.
- If λ ≠ μ, take the largest part value c whose multiplicities differ. Then the difference is dominated by ±c^t for large t, so it cannot vanish at all 2^j. Therefore λ = μ.

**The result is already published.** Stella Li, *A note on multiset reconstruction from sum and pairwise products*, arXiv:2508.00971 (receipts in `sources/`), plus a 2026 *Integers* note. It earns zero credit. Lean was not pursued.

### 365134 — Mkrtchyan Conjecture 8 (non-conflicting Z₂×Z₂ flows, Hamiltonian path)

This is the strongest finite route, but no counterexample was found. Details are in `results.json` and `SUMMARY.md`.

If a witness is found later, the Lean plan would be a pure finite certificate:

- **Definitions:**
  - a loopless cubic multigraph as an explicit edge list on `Fin n`;
  - `HasHamPath` (witnessed by an explicit vertex order);
  - `Bridgeless`;
  - `PerfectMatching`;
  - the complementary 2-factor's cycles (as connected components of the complement);
  - the labelling predicate (cycle sums in `ZMod 2 × ZMod 2`, plus the no-{a,b} edge condition).
- **Endpoint:**

  `¬ ∀ G, Bridgeless G → HasHamPath G → G ≠ Petersen → ∃ F, PerfectMatching G F ∧ ∃ θ, NonConflictingFlow G F θ`

  established by an explicit witness G. "Not isomorphic to Petersen" would be certified by a vertex count (G has n ≠ 10). Non-existence would follow by `decide` over all perfect matchings × 3^{n/2} labellings, or better by a proved-sound checker evaluated with kernel `decide`. For n ≈ 30 that is large: per-perfect-matching parity and conflict lemmas would be needed to keep kernel reduction feasible.
- **Semantic bridge:** the source contracts F̄ to get G/F̄ (a pseudograph) and puts a nowhere-zero flow on it. The bridge must prove that a nowhere-zero Z₂×Z₂-flow on G/F̄ is exactly an F-edge labelling whose sum vanishes on each F̄-cycle. A loop contributes 2θ = 0; orientation is irrelevant in characteristic 2.

The uncompiled sketch stops here because no witness exists to certify.
