# Root integration interfaces

Namespace is `Polyomino57`. Source copies are in `formal/`; the frozen replay uses `extracted/formal/` and actual compiled artifacts live only under `extracted/work/`.

Closed and immediately reusable:

```
normalizedSquare_universal (n : ℕ) (hn : 0 < n) :
  UniversalContainer n (normalizedSquare n)
eligible_positive (n : ℕ) (hn : 0 < n) : EligibleSize n (n*n)
minimumSize_realized (n : ℕ) (hn : 0 < n) : EligibleSize n (minimumSize n)
minimumSize_is_least (n : ℕ) (hn : 0 < n) :
  EligibleSize n (minimumSize n) ∧ ∀ m, EligibleSize n m → minimumSize n ≤ m
numericPlacement_iff (P : List GridPoint) (t : GridPoint) :
  numericPlacement P t = true ↔ translate t P.toFinset ⊆ witness
grown_normalized_mem (h : Grown P) :
  normalize P (growth_sound h).1 ∈ generatedLayer (P.card-1)
```

For closure certificates, `successorRowCheck next row choice` checks every grid neighbor of every source cell, ignores neighbors already occupied, then uses the supplied index/translation to check translated point-list equality in the next array. `edgeCheck` checks array bounds; a bad index returns false. Equality is semantic set equality, without sorting/distinctness hypotheses. It is important not to demand `normalize raw = target` as an externally assumed fact: `edgeCheck_sound` proves normalized equality from the actual checked translation.

`represented_growth_step` transfers arbitrary Grown steps to these checked representatives, covering changes of normalization origin and negative insertions. `certificate_growth_coverage` iterates it. The computed `generatedLayer` is not blindly expanded to size 11.

Conditional terminal assembly takes exactly:

```
L : ℕ → Array (List GridPoint)
choices : ℕ → List GridPoint → GridPoint → ℕ × GridPoint
shifts : List GridPoint → GridPoint
base : [(0,0)] ∈ (L 0).toList
steps : ∀ k < 10, arrayClosureCheck (L k) (L (k+1)) (choices k) = true
terminal : arrayTerminalCheck (L 10) shifts = true
```

and proves `UniversalContainer 11 witness`, then `¬ SourceFormula`. These premises are NOT all discharged here. The 133 separately replayed terminal forests check actual supplied placements, but do not yet furnish `terminal` for an identified `L 10` or its `steps`. Their public endpoints are `TerminalNNN_checked` and `TerminalNNN_sound`; `TreeMember` is literal occurrence in the finite tree, not connected-family membership.

The mandatory remaining bridge is finite kernel-certified successor closure from five through eleven cells, plus equality/translation correspondence between that certified terminal representation and the checked placement forest. No cardinality-of-animal-family theorem is needed by the generic assembly and no external Python count can replace closure.

The optional sorted-list add-on uses lexicographic insertion and one list equality, proving its fast row checker implies the established row checker. Its receipt determines whether it is compiled/audited; it is separate from the main frozen archive. It needs no sortedness hypothesis for soundness, though sorted input is necessary for this stronger equality check to succeed on the intended data.
