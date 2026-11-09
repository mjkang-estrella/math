
## 6. Tamper tests (task 5)

`tamper_F.py`, `tamper2_F.py` build corrupted copies of real certificates (in `tamper/`) and run `check_sym_F`. Base certificates used: `decimal5_high/K1943_…` (contains sumset leaves; 450 588 lifts), `decimal_full/K5723_…` (tail kills, repeated residues; 9 290 lifts), `broad_pin2/K2087_…` (pin2 only). Unmodified bases: **ACCEPTED** (4/4). `cmp_tamper.py` also ran M's `check_sym.py` on every file (last column).

| tamper | modification | mine | first reason given | M's check_sym |
|---|---|---|---|---|
| `sumset_leaf_prime_swapped` | sumset leaf 295 prime 196482241(sumset/tail)->11 | **REJECTED** | leaf 295: prime 11 does not kill | FAIL |
| `sumset_leaf_class_shifted` | sumset leaf 295 residue shifted | **REJECTED** | node 291: lift (249, (35, 99, 228, 345), (349,), (36,)) mod 432 neither child nor killed | FAIL |
| `sumset_single_representative` | leaf 295: prime 41 kills if residue is taken as the exponent (single rep) but not over the full sumset | **REJECTED** | leaf 295: prime 41 does not kill | FAIL |
| `tail_pin_removed` | meta pin_digits 3 -> none (kills that need the coset must fail) | **REJECTED** | node 1: lift (2, (4, 4, 4), (2, 2)) mod 6 neither child nor killed | FAIL |
| `tail_pin_too_wide` | pin_digits=4 > min(3,qmin) (classic over-pin) | **REJECTED** | pin_digits out of range | FAIL |
| `tail_qmin_below_pin` | qmin=2 with pin_digits=3 (pin beyond minimum position) | **REJECTED** | pin2 requires qmin >= t0+3 | FAIL |
| `tail_K_plus_9000` | K += 9000 (same K mod 9 and mod 1000: only the other primes see it) | **REJECTED** | node 0: lift (0, (1, 1, 1), (1, 1)) mod 2 neither child nor killed | FAIL |
| `tail_K_plus_18000` | K += 18000 (same K mod 9 and mod 1000: only the other primes see it) | **REJECTED** | node 0: lift (0, (1, 1, 1), (0, 1)) mod 2 neither child nor killed | FAIL |
| `INFO_K_plus_1000` | INFORMATIONAL: K+=1000 changes K mod 9 => a=0 exact, impossible with the pin => vacuously closed | **ACCEPTED** |  | PASS |
| `INFO_pin2_flipped_with_tail` | INFORMATIONAL: pin2 off while tail k=3,t0=0 (tail already implies mod 8) | **ACCEPTED** |  | PASS |
| `pin2_removed_no_tail` | cert with pin2 only: pin2 -> false | **REJECTED** | node 0: lift (0, (1, 1, 1), (0, 1)) mod 2 neither child nor killed | FAIL |
| `pin2_qmin_too_small` | pin2 with qmin=2 < t0+3 | **REJECTED** | pin2 requires qmin >= t0+3 | FAIL |
| `multiset_child_deleted` | node 0: first child removed from c | **REJECTED** | node 0: lift (0, (0, 0, 0), (0, 0)) mod 2 neither child nor killed | FAIL |
| `multiset_child_duplicated` | node 0: duplicate child id | **REJECTED** | duplicate child class at 0 | FAIL |
| `multiset_child_not_a_lift` | child 1: one residue +1 (reduction mod parent changes) | **REJECTED** | duplicate child class at 0 | FAIL |
| `multiset_child_class_swapped` | child 1 given sibling 2 class | **REJECTED** | duplicate child class at 0 | FAIL |
| `multiset_rest_emptied` | node 0: rest primes removed | **REJECTED** | node 0: lift (0, (1, 1, 1), (1, 1)) mod 2 neither child nor killed | FAIL |
| `multiset_repeat_split_wrong` | node 1: one copy of a repeated residue moved | **REJECTED** | duplicate child class at 0 | FAIL |
| `ms_repeat_to_other_lift_4` | child 11: one of the equal residues 2 moved to the other lift 4 (still a lift of the parent) | **REJECTED** | node 2: lift (2, (2, 2, 4), (1, 2)) mod 6 neither child nor killed | FAIL |
| `ms_multiplicity_not_preserved` | child 11: one copy of repeated residue 2 replaced by 3 (reduction mod 2 changes) | **REJECTED** | node 2: lift (2, (2, 2, 4), (1, 2)) mod 6 neither child nor killed | FAIL |
| `ms_deep_child_deleted` | node 2: child 11 removed | **REJECTED** | node 2: lift (2, (2, 2, 4), (1, 2)) mod 6 neither child nor killed | FAIL |
| `ms_deep_rest_weak` | node 2: rest primes replaced by [101] | **REJECTED** | node 2: lift (2, (4, 4, 4), (3, 4)) mod 6 neither child nor killed | FAIL |
| `tail_qmin2_pin2off` | qmin=2 with pin_digits=3 and pin2 off (isolated over-pin: pin deeper than the smallest allowed position) | **REJECTED** | pin_digits out of range | FAIL |

Notes.
* **Required three** — a corrupted sumset-kill leaf (`sumset_leaf_prime_swapped`, `sumset_leaf_class_shifted`, and the targeted `sumset_single_representative`: a prime that would kill if each residue were treated as the exact exponent mod `d` — the classic over-optimistic sumset — but does **not** kill over the full sumset; the checker rejects it), a corrupted tail-coset (`tail_pin_removed`: kills that need the coset fail; `tail_pin_too_wide`/`tail_qmin_below_pin`/`tail_qmin2_pin2off`: the "pin deeper than the smallest position" error (k > min(3, qmin)) is rejected at the meta level — the last one isolates it from pin2; `tail_K_plus_9000/18000`: K changed in a way invisible to the mod-9/mod-1000 data, so only the other primes can notice — rejected), and a corrupted multiset child (`multiset_*` and `ms_*`: deleted child, duplicated child, child class swapped with a sibling, residue not reducing to the parent, a repeated residue pair split wrongly, a different genuine lift in place of the true one, `rest` primes emptied/weakened) — **all rejected**.
* Two informational cases are (correctly) **accepted**: `INFO_K_plus_1000` changes `K mod 9`, so `v3(X)=0` exactly, which is incompatible with the tail coset (`3^a7^w ≡ K/2^{t0} mod 1000` forces `a ≡ 3 mod 10`): the configuration is then closed vacuously by the pins; `K += 8` likewise makes the target non-representable mod 1000 (empty pair set). `pin2` toggled off while `k = 3`, `t0 = 0` is also accepted because the tail modulus 1000 already contains the mod-8 information. Both checkers agree on these.
* K-sensitivity of the checker was also verified positively: planting a genuine smooth solution (`K := 3^a7^w − X_0` for random placements) and keeping the same tree is **rejected** in 12/12 trials (the unlisted lift containing the planted solution is not killed), so the acceptance of the real certificates is not an artefact of leniency.
* M's own tamper directory consists of dimension-1 `scope=class` controls plus a few full trees; the dim-1/class files are outside my checker's scope by design (I reject `scope != full`) and are not used.
