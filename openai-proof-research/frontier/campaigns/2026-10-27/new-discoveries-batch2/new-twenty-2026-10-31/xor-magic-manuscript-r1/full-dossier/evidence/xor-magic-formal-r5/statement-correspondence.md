# Statement correspondence — MathDB 372205

The source is arXiv:2512.19278v1, Conjecture 25, with the root's corrected-scope ruling in the hash-bound inputs. This packet proves the corrected existence statement and refutes the literal printed statement. It does not prove the printed statement.

| Source or intended mathematical requirement | Literal Lean representation | Final theorem or bridge |
|---|---|---|
| Vertex labels in (Z/2)^n, bijective | `Bits n := Fin n → ZMod 2`, equivalence `V ≃ Bits n` | `Literal`, `card_of_label` |
| Simple, connected, zero open neighbourhood sum | `SimpleGraph V`, `OpenMagic G n` | `Literal` |
| Simple, connected, zero closed neighbourhood sum | `ClosedMagic G n` | `Literal` |
| d-regular, order 2^n | `G.IsRegularOfDegree d`, cardinality from labels | `OpenExists`, `ClosedExists` |
| All odd 5 ≤ d ≤ 2^n−5, all even 4 ≤ d ≤ 2^n−6, for n ≥ 4 | `∀ n : ℕ, 4 ≤ n → CorrectedAt n` | `XorMagic.corrected_all` |
| Printed closed upper endpoint 2^n−4 is impossible for every n ≥ 4 | `∀ n : ℕ, 4 ≤ n → ¬ PrintedAt n` | `XorMagic.not_printed_each_ge_four` |
| Literal negation without connectivity assumption | zero closed sums and bijection imply false at degree 2^n−4 | `XorMagicFinal.no_closed_top_four_any` |
| All-n and positive-n printed assertions are false | exact universal negations | `XorMagic.printed_not_all`, `XorMagic.printed_not_positive` |

The walk is retained from the fixed-point lift rather than reconstructed from an arbitrary indexed cycle. `seedOfRelabelledWalk` transports this actual walk, its cycle proof, exact length and every indexed vertex. `ColouredCycleData.omegaWalk` derives the next `OmegaWalk` from the indexed outgoing certificate. This supplies the required iteration bridge without an unnecessary general walk-existence theorem.

Hazards H1–H7: genuine `IsCycle` and length ≥ 3 are retained; global chosen slopes and reverse direction are inherited unchanged; the same oriented incidence maps are used; complement factors come from the full disjoint block decomposition; interpolation uses the inherited two-case connectivity proof; n = 4 and n = 5 use direct `corrected_at_4/5`; `seeds_all` has two distinct bases and decrements n by 2, and `main_ranges` uses the n−2 seed only for n ≥ 6.

No publication, credit, prior-art clearance or root acceptance is asserted here. The prior-art and manuscript qualifications in the root ruling and review remain the root's responsibility.
