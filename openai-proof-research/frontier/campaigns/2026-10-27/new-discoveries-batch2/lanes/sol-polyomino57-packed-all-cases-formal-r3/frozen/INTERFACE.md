All new generic names are in `Polyomino57.Diagonal.FiniteProof.Packed`.

- `digit a i`: i-th radix-64 digit, recursively dividing by 64.
- `mergeCheck_sound`: a recursive Boolean row check implies every coordinate inequality.
- `rep n`: sum of the n radix powers (recursive `1+64*rep n`).
- `bounded n a`: a has exactly n or fewer radix digits, all at most 12; zero rows allowed.
- `bounded_le`: bounded n a implies a ≤ 12*rep n.
- `slack n a b c = a+b+32*rep n-c-rep n` (Nat subtraction).
- `slack_step`: under boundedness, slack at n+1 equals `(a%64+b%64+31-c%64)+64*slack n (a/64) (b/64) (c/64)`; low digit lies below 64.
- `bits_sound`: bounded n a, bounded n b, bounded n c, and `(slack n a b c &&& (32*rep n))=32*rep n` imply `mergeCheck n a b c=true`.
- `boundCheck_sound`: executable radix digit-bound check gives bounded.
- `checkedPairs_sound`: `checkedPairs n c pairs=true` and `(a,b)∈pairs` imply `∀i<n, digit c i+1≤digit a i+digit b i`.
- `bits_certificate`: n, idx:V→Nat, finite D,M, E,H,row:(Finset I→Nat); idx<n on D; bounded rows for every nonempty A⊆M; exact base and edge inequalities for digit(row A)(idx v); bitCheck for ALL ordered disjoint nonempty A,B⊆M. Conclusion is the frozen GraphPotential.Certificate E D M H (fun A v=>digit(row A)(idx v)). No powerset reducer, masks, symmetry, or geometry premise is silently inferred.
- `PackedFull.coordinate_merge`: for every pair (a,b) in the concatenation of PackedFull0.pairs through PackedFull7.pairs, and i<24, the explicit frozen full-row digit +1 is at most digit a i+digit b i. Full row is a literal natural in the actual printed type. Exact types and allowed axioms are printed in the replay audit.

Unchanged literal endpoint interfaces are in frozen/INTERFACE.md and formal/Completed.lean. RemainingCases is still unproved and has 33 cases. The sole conditional universal theorem remains `Completed.universalContainer_of_remaining` (namespace FiniteProof, no module-name prefix). Full mathematical domain/group and source-placement semantics are unchanged.
