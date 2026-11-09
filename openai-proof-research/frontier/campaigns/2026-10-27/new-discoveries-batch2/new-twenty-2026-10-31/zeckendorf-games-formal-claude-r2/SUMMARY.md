# MathDB 347063: Lean formalization, second lane

Credit 0. Campaign 58 of 80 unchanged. Root alone decides acceptance, and acceptance may be refused. Nothing here claims credit.

## Result

Both target theorems are proved in Lean, with no premise added and the sealed game unchanged.

```lean
theorem Zeck.split_smallest_asymptotic :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → |(SS n : ℝ) - phi ^ 2 * n| ≤ C * (Real.log n) ^ 2

theorem Zeck.combine_smallest_asymptotic :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      |(CS n : ℝ) - (5 / 2 - phi + ∑' j : ℕ, 1 / (F (2 * (j + 2)) : ℝ)) * n|
        ≤ C * Real.sqrt n * Real.log n

theorem Zeck.combine_constant_bracket :
    (1.206 : ℝ) < 5 / 2 - phi + ∑' j : ℕ, 1 / (F (2 * (j + 2)) : ℝ) ∧
      5 / 2 - phi + ∑' j : ℕ, 1 / (F (2 * (j + 2)) : ℝ) < 1.207
```

Here `phi = (1 + √5) / 2`, and `F` is the sealed source indexing (`F 1 = 1`, `F 2 = 2`, `F 4 = 5`). The tsum index `j` starts at 0, so it runs over `F_4, F_6, …`, the source sum over `j ≥ 2`.

## Evidence

Fourteen new modules. Each has a passing compile through `check32.sh`, a passing kernel check through `checker32.sh`, and an axiom audit compiled through `check32.sh`. `results/347063.json` lists source and olean hashes and labels.

| Module | Content |
|---|---|
| `ZeckMoves` | Reachability with exact counts, the tail bound `CSfrom a ≤ Phi a`, the counter `D`, combine and split equations |
| `ZeckWindow` | Six-count windows, the four window combines |
| `ZeckLow` | Pool splits, low moves, the insertion `cascade`, `pending` |
| `ZeckMacro` | READY state `B`, `macro_step`, `macro_step0`, the loop lemmas |
| `ZeckExit` | Endgame at level `p ≥ 4`, by K and by Case 1, 2, 3 |
| `ZeckLevel` | Level-2 endgame, `level_step`, start phase, low-state bounds |
| `ZeckConst` | The constant, tsum tail, bracket |
| `ZeckChain` | `chain`: moves minus counter over the levels |
| `ZeckCS` | `CS_large`, `CS_estimate` |
| `ZeckSS` | Split Smallest lower half, `SS_estimate` |
| `ZeckEndpoint` | The three statements above |
| `ZeckAudit2`, `ZeckAudit3` | `#print axioms` on every main theorem |
| `ZeckRotation` | Rotation and cycle balance (see below) |

`#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for every audited theorem. A scan of all new sources found no `sorry`, `admit`, `native_decide`, `unsafe` or `axiom` declaration.

All Lean ran through the two wrappers, one at a time, inside the lane's limits. Nine failed compiles are kept with their true exits: `moves01`, `moves02`, `moves03`, `win01`, `low01`, `const01`, `cs01`, `ss01`, `rot01`. They were elaboration failures fixed by changed sources, each with a new label. Every failed run ended with exit 1 and was not retried unchanged.

## How the proof goes, and one route deviation

The endpoint proof departs from the route in one place. The route counts splits with a rotation and cycle balance. Our proof uses an integer counter instead: `D a = Σ a_i d_i` with `d_i = F_{i-2} - [i even]`. `D` rises by exactly one on every split and every even-index combine, and is unchanged by odd-index combines and by `A1`. So at every level, moves equal the counter's rise plus the number of odd combines, which equals the growth of the next pool up to a bounded error.

The rotation and chip balance were still proved, as the route asks, in `ZeckRotation`, but `ZeckEndpoint` does not import that module:

- `macro_rotation`: a macro sends the low value to `(val z + F q) % F (q + 1)`, that is `L ↦ L + F_{p-2} mod F_{p-1}`, with `p = q + 2`.
- `rotation_cycle`: over one cycle, from `B z q m h` with `5 * F (q+1) ≤ m`, the low state returns, the pool loses `F_{p+2}`, the pile gains `F_p`, the cycle has `F_{p+2} - 1` moves, and `splitCount` over those moves is `F_p - 1`.

`splitCount` is defined from the actual run: at each position it counts the step exactly when `stepCS` has no `A1`, no combine and a legal split. `Steps_chips` proves that chips lost plus splits equals moves.

## The endgame

`exit_step` follows the erratum: K = 0 and 1 are relabellings; K = 2 and 3 are split into Case 2 versus Cases 1 and 3; K = 4 is split into Case 1, Case 2, and Case 3, with the q = 2 branch separate. The corrected K = 3 Case 3 entry fires `C_{p+1}` before `S_{p-2}` and ends at `B z' (q+2) (M+1) 0`, as in the erratum.

## Unpaid

- The endpoint binds to the source game: `n` chips of value `F 1` (`Zeck.start`). The MathDB record says the game starts from the Zeckendorf decomposition, where no move is legal, as `ZeckControls` records. Root must rule on this binding.
- Independent statement-fidelity review, a paper, further prior-art work and a fresh extracted replay are outside this lane and were not done.
- The route asked for mathlib's Zeckendorf API where it fits. The low state uses this lane's own `Zk` with `val` and `Zk.eq_of_val` instead, so `Nat.zeckendorf` and its index shift are not engaged.
- Part (a) is public; it remains attributed and uncredited.

Status: both target theorems compiled and kernel-checked in this lane. No credit claimed.
