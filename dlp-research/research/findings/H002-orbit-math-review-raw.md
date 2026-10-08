# Unaccepted H002 delegated report: orbit-math-review

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h002-orbit-math-review-20261008-r1`.
Provider/model: `claudeAgent/claude-opus-5-5`; status completed.

This report is retained for process evidence, not automatically adopted. Primary
formula checks, cost assumptions and universal claims require coordinator
qualification. In particular the EDS index1 identity is under active correction;
no experiment should rely on it before resolution. See the coordinator disposition.

# Review of H002 A3: fast large-orbit canonicalization with a transporter

**Verdict:** A3 has no executable fast rule. The proposed Lattès pruning has nothing to prune inside the prime-order group. The card also aims at the wrong bottleneck. A transporter does not have to run at every step. The hard object is a cheap label that stays fixed across an orbit and separates different orbits.

## 1. What canonicalization actually requires (correction to the card)

The card says "a fingerprint without a transporter does not suffice". That is only true for the additive r-adding walk it implicitly assumes.

- **Additive walk** `X → can(X) + R_h`:
  - Each step needs a class-invariant representative `can(X)`.
  - It does not need the transporter `t` online. With distinguished points (DPs), you can recompute the `t` values later, only along the two colliding trajectories. Each trajectory is about `1/θ` steps long, where θ is the DP probability.
  - Post-hoc recovery then costs about `(2/θ)·C_tr`, with `C_tr` up to about √m (baby-step giant-step inside H).
  - So the card's rejection rule "spends √m recovering the multiplier" is fatal only per online step, not post-hoc.
- **Multiplicative walk** `X → c_{h(F(X))}·X`, with small integer multipliers `c_i` and several random starts `a_j P + b_j Q`:
  - H acts by scalars, so scalar multiplication commutes with H. A plain H-invariant label F is enough to make the walk well defined on classes.
  - A collision `uY ~ vY'` gives `u(a+bk) = λ^s v(a'+b'k)`. You need s only once per collision (cost ≈ √m), then solve for k linearly.
  - In exponent form this is Teske's r-adding walk on the cyclic group `(Z/n)*/H`.
  - Short fruitless cycles need a product of the `c_i` to land in H. If `c_i ≤ c`, that needs about `log n / log c` steps or more.
  - Self-collisions inside one walk carry no information, so you need parallel collision search with distinct starts (van Oorschot–Wiener). Single-walk Floyd fails.
  - I haven't checked prior art for this walk; treat its novelty as unknown.

**Corrected cost:** `W_pre + (C_F + C_step)·√(πn/(2m)) + N_coll·C_tr(m)`.

- `N_coll` must include false collisions when F is not injective on classes. Each false collision costs one failed √m transporter search.
- The baseline is `C_rho·√(πn/(2g0))`, with H required to contain the automorphisms μ so the comparison is matched.

**Consequence (heuristic, generic-model only):** a label F computable in polylog time for m ≈ √n would give about `n^{1/4}·polylog` total work. Shoup's generic bound (Eurocrypt 1997) then forces any *generic* label to cost about `C_F ≳ √m/polylog`. This assumes the random-walk heuristic. It does **not** exclude a coordinate-based label. It only shows that A3 is equivalent to building a fast non-generic orbit label. The transporter is not the obstacle.

## 2. Exact obstruction: small m needs a high-degree endomorphism

**Lemma.** Let `α ∈ End(E)` act by λ on `E(F_p)` (cyclic of prime order n), with `λ^m ≡ 1 (mod n)` and `α^m ≠ 1`. Then `(deg α)^{m/2} + 1 ≥ √n`.

**Proof.** `α^m − 1` kills `ker(π−1)`, and `π−1` is separable. So `α^m − 1 = γ∘(π−1)` and `deg(α^m − 1) ≥ n`. Also `deg = |·|²` and `|α^m − 1| ≤ |α|^m + 1`. ∎

So there are two cases:
- **Roots of unity** (m ≤ 6): these are the automorphisms, already counted in g0.
- **Everything else:** `m ≥ ≈ log n / log(deg α)`. For a 256-bit n and `deg ≤ 2^8`, that means m ≥ 32. Multiplication by 2 (`H = ⟨±2⟩`) is a special case: `ord_n(2) ≥ log₂ n`, and it is typically about n.

**Consequence for orbit enumeration.** This needs an extra cost-model assumption: a degree-d endomorphism costs at least about `c·log d`, e.g. evaluated as a chain of small isogenies. Then enumerating the orbit costs `C_can ≥ max(c·log₂ n, m·c_min)`.

Beating the baseline would need `c·log₂n·√g0 / C_rho < √m < C_rho / (c_min·√g0)`. That requires `C_rho² > c·c_min·g0·log₂ n`, which is about 512 at 256 bits. With C_rho around one point addition, this fails by more than an order of magnitude. Every enumerating canonicalizer loses at cryptographic sizes. This rules out implementations, not coordinates in general.

## 3. Lattès / division-polynomial pruning: no executable rule, and an exact obstruction

Take the concrete map `f₂(x) = x(2P)` restricted to `x(E(F_p)∖{O})`, with n an odd prime:
- **In-degree is exactly 1.** One preimage comes from halving. The other three, `x(R+T)` with T a 2-torsion point, are F_p-rational only if `2R ∈ E[2] ∩ E(F_p) = {O}`. The twist's x-values are disjoint, because the cubic has no root in F_p.
- So the F_p-rational backward graph inside the subgroup is a **union of cycles of length m′ = ord of 2 in (Z/n)*/{±1}**. A recursive pruning over it degenerates to a linear walk around the cycle. Branching exists only over F̄_p, where degrees grow like `4^j`, and the card gives no rule there.
- **Orbit-polynomial representation.** `Φ(T) = ∏(T − x(2^j X))` has degree m′. Building it, storing it, or finding its minimum root is Ω(m′). It is a factor of `f^{(m′)}(T) − T`, which has degree `4^{m′}`.
- "Minimum" under the integer order of F_p is not Galois-stable or algebraic. For non-automorphism α there is no finite quotient curve E/⟨α⟩, so there is no low-degree rational invariant (unlike `x², x³` for j = 1728 or j = 0).

## 4. Smallest falsifiers (none run, by instruction)

1. **Lattès in-degree claim:** on toy prime-order curves (p around 10³–10⁴), compute every F_p-rational f₂-preimage of every `x ∈ x(E(F_p))` and confirm in-degree 1 and cycle length m′.
2. **Lemma check:** on toy CM curves with a degree-2 endomorphism (D = −7, j = −3375, eigenvalue a root of `x² − x + 2` mod n), compute `ord(λ)` and confirm `m ≥ log n/log 2`.
3. **Requirement correction:** on toy curves with `H = {±1}` and `F = x`, run the multiplicative walk with r ≈ 16–20 multipliers. Compare total steps to `√(πn/4)` against the additive negation baseline, counting fruitless cycles and false collisions. A mismatch would falsify the claim that one end-of-run transporter is enough.

## Unresolved

- Whether any coordinate-based H-invariant label exists for non-automorphism H with `C_F ≪ √m`. The section 2 and 3 obstructions do not settle this.
- Literature status of the multiplicative-walk / label-only formulation.
- Representation size and DP-memory trade-offs if F is a lossy hash.

**Sources:** the lemma and the in-degree argument are elementary and proved above. Background: Shoup (Eurocrypt 1997), Teske (Math. Comp. 70, 2001), van Oorschot–Wiener (J. Cryptology 1999), Duursma–Gaudry–Morain (ASIACRYPT 1999). I did not fetch any sources in this read-only review; the citations are from memory. I made no repo edits and ran no experiments.
