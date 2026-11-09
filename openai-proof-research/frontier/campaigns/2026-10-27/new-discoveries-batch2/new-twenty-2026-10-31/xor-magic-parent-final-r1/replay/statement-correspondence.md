

The Lean dossier uses the following definitions verbatim from Literal.lean. The context is V : Type with Fintype V and DecidableEq V; each graph has a decidable adjacency relation. Natural subtraction is harmless in the advertised n >= 4 range. A simple graph is part of the type, connectedness is explicit, and the equivalence supplies every label exactly once.

    abbrev Bits (n : Nat) := Fin n -> ZMod 2

The six literal definitions are displayed on the next page using the original Lean notation. Their type quantifiers prevent the existential graph from being fixed in advance: the witness may depend on n and on the requested degree d. The finite underlying type is allowed to vary. No construction hypothesis, unproved seed premise, or assumed connectivity remains in the final endpoints.

The main theorem is XorMagic.corrected_all : forall n : Nat, 4 <= n -> CorrectedAt n. The second endpoint is XorMagic.not_printed_each_ge_four : forall n : Nat, 4 <= n -> not (PrintedAt n). The latter is a pointwise impossibility assertion at every exponent in scope, stronger than merely finding one failure of the universal printed claim. The re-exports printed_not_all and printed_not_positive also negate the unrestricted and positive-exponent readings. These statements have different scientific roles: only the corrected existence theorem supplies the substantive construction.
<!-- PAGE -->
## 7. Literal definitions (continued)

    def OpenMagic (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) : Prop :=

      G.Connected ∧ ∃ l : V ≃ Bits n, ∀ v, ∑ u ∈ G.neighborFinset v, l u = 0

    

    def ClosedMagic (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) : Prop :=

      G.Connected ∧ ∃ l : V ≃ Bits n, ∀ v, l v + ∑ u ∈ G.neighborFinset v, l u = 0

    

    def OpenExists (n d : ℕ) : Prop :=

      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V)

        (_ : DecidableRel G.Adj), G.IsRegularOfDegree d ∧ OpenMagic G n

    

    def ClosedExists (n d : ℕ) : Prop :=

      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V)

        (_ : DecidableRel G.Adj), G.IsRegularOfDegree d ∧ ClosedMagic G n

    

    def PrintedAt (n : ℕ) : Prop :=

      (∀ d, Odd d → 5 ≤ d → d ≤ 2^n-5 → OpenExists n d) ∧

      (∀ d, Even d → 4 ≤ d → d ≤ 2^n-4 → ClosedExists n d)

    

    def CorrectedAt (n : ℕ) : Prop :=

      (∀ d, Odd d → 5 ≤ d → d ≤ 2^n-5 → OpenExists n d) ∧

      (∀ d, Even d → 4 ≤ d → d ≤ 2^n-6 → ClosedExists n d)

The namespace of these definitions is XorMagic. The declarations appear without alterations in the source-only packet; all 107 Lean modules are byte-identical to xor-magic-formal-r5/formal. The prose expansion on the previous page explains the binders but does not replace the literal source.

In particular OpenMagic and ClosedMagic conjoin connectedness with existence of a bijective zero-sum labeling. OpenExists and ClosedExists additionally quantify the simple graph and demand degree regularity. PrintedAt includes the forbidden closed upper bound; CorrectedAt changes that bound to 2^n-6 and preserves the entire open range. Finite decidability instances are elaboration data and do not weaken these propositions.
<!-- PAGE -->
## 8. Correspondence, replay, and trust

Paper statement | Lean declaration (namespace prefix XorMagic unless shown)
Total sum; complement identity | total_bits; complement_identity
Literal graph definitions | Literal: OpenMagic, ClosedMagic, OpenExists, ClosedExists
Seed and orientation | ColouredSeed; FactorColouring; chosen_outgoing
Translation choice (Section 3) | translation_exists; TranslationFour module
Component fibre argument | EdgeTransport.fibre_transport; fibre_card_reachable;
section_of_singleton; section_of_three; connected_of_affine_loop
Matching/cycle/color persistence | persistedCycle; ColourPersistence, ComplementDecomposition
Interpolation and intervals | InterpAssembly, InterpEndpoints, InterpolationArithmetic
Direct finite bases | Base*.connected; corrected_at_4; corrected_at_5
Two induction bases | seeds_all; main_ranges
Theorem 1 | corrected_all : ∀ n : ℕ, 4 ≤ n → CorrectedAt n
Theorem 2 | not_printed_each_ge_four : ∀ n : ℕ, 4 ≤ n → ¬ PrintedAt n
Universal printed negations | printed_not_all; printed_not_positive

Only propext, Classical.choice and Quot.sound are allowed as transitive axioms. The packet's audits inspect local declarations, full types and bodies, safety flags and transitive axioms, including auxiliary declarations. Shared expression DAGs are checked independently; duplicate generated declarations must have identical canonical type and body hashes. No sorry, admit, new axioms, unsafe, native_decide or ofReduceBool is permitted in the delivered proof modules. The audit does not reinterpret upstream mathlib theorems.

The pinned installation is Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52. The read-only package cache uses mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. Set LEAN_BIN and LEAN_PACKAGES as documented in REPRODUCE.md. The portable driver rejects existing oleans, checks source hashes, discards inherited Lean configuration, retains actual HOME, and writes logs and per-call receipts. Each module is compiled with -j1 -DwarningAsError=true, then checked by leanchecker. The extraction is fresh and path-safe. All deletions, if any, are confined to driver-owned temporary files; this version requires no cleanup deletions.

Each child invocation has affinity to at most two CPUs, 120 CPU seconds, a 140-second wall guard, aggregate sampled RSS <= 6 GiB and MALLOC_ARENA_MAX=2. Upstream cached oleans are trusted. leanchecker shares the same installation; it is an additional check, not an independent implementation of Lean's kernel. Sampling RSS is not a continuous hardware-enforced memory measurement.

Negative controls deliberately corrupt concrete arithmetic, labels, sums, degrees, seed and coloring facts, slope/reverse/composition facts, incidence and holonomy facts, the top endpoint and the inference from CorrectedAt to PrintedAt. Their rejection demonstrates only rejection of these particular false claims with imports resolved; it does not prove the completeness of the audit or guard against every possible specification error. The source-only archive contains no oleans. The full dossier adds the manuscript, evidence, QA images, receipts and manifests. Replay results and hashes are recorded outside this static draft in results.json and SUMMARY.md. Root must perform the final replay and paper review before any acceptance.
<!-- PAGE -->
