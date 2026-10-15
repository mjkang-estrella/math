# Exact formal coverage map

All theorem names below are in namespace `KineticSupport`. Line numbers refer to the authenticated 109-line `KineticSupport.lean`. Except for the replacement lemma, `E` has `[NormedAddCommGroup E] [InnerProductSpace ℝ E]`. The intended physical specialization is the real Euclidean three-dimensional velocity/position space. No theorem silently assumes an analytic kinetic result.

| Declaration and line | Exact hypotheses and conclusion | Repaired candidate use | Unformalized boundary |
|---|---|---|---|
| `collision_momentum`, 19 | All `v,w,n`; the two outgoing velocities sum to `v+w` | Elastic C-update in Lemma W §2.2 | Physical contact existence, flux and histories |
| `collision_energy`, 24 | All `v,w,n` with `<n,n>=1`; sum of the two outgoing squared norms equals the incoming sum | Pair energy in §2.2 | Unit normal obtained from an actual sphere contact; no arbitrary nonunit extension |
| `affine_time_shift`, 34 | All `a,v,t,shift`; `(a-shift*v)+t*v = a+(t-shift)*v` | Pre-first segment origin transformation in §2.3 Claim 2 | Actual scattered paths and all-event covariance |
| `relative_origin_shift`, 40 | All `a,b,v,w,shift`; relative origin changes by `-shift*(w-v)` | Initial forest `y_l=A_q-A_p` shear in §2.3 | Forest solvability, chart construction and measure theory |
| `contact_time_shift`, 47 | All `a,b,v,w,t,shift`; relative position at new `t+shift` equals that at old `t` | Local contact equation under Claim 2's common-time shift | Selection/covariance of the entering root and its forward bound; global chronology |
| `affine_shift_compose`, 55 | All `a,v,s,t`; two origin shears sum to the shear by `s+t` | Affine shear composition underlying §2.3 | Complete history action, inversion and Jacobian |
| `total_energy_of_pair_replacement`, 63 | `E` only normed additive commutative; finite decidable label type, `i!=j`, unchanged outside pair, local pair squared-norm equality; full finite sum equality | All-line accounting in §2.2 | Does not itself establish local pair conservation or any event sequence |
| `total_collision_energy`, 92 | Finite decidable label type, old vector `u`, distinct labels, `<n,n>=1`; concrete nested update preserves the full sum | One C-step of §2.2 all-line energy invariant | Finite-event induction and successful all-time path construction |
| `exponent_budget`, 103 | No mathematical hypotheses; the three displayed rational equalities/inequality | §5 chaining and §6 exact-centering transfer | Real-power identities, moment estimates, limits and tightness |

The update definitions are `leftVelocity` at line 13, `rightVelocity` at line 16, and `pairVelocity` at line 86. `pairVelocity u i j n` changes the value at `i` to `leftVelocity (u i) (u j) n` and at `j` to `rightVelocity (u i) (u j) n`, using the old `u` in both expressions. The independent `old_left` and `old_right` theorems check these evaluations explicitly. `old_left` needs `i!=j` so the final update at `j` does not overwrite `i`.

The author source contains exactly nine `theorem` declarations and three `noncomputable def` declarations. The independent audit adds nine exact-type wrappers, two evaluation lemmas, and three concrete semantic counterchecks; these are validation artifacts, not additions to the advertised package or new frontier results.
