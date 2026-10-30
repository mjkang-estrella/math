# Lean proofs for the symmetric `L_p` Rogers--Shephard conjectures

This repository contains independent Lean 4 proofs of Conjectures 4 and 5 from
[Fradelizi--Manui--Meyer--Ndiaye, arXiv:2607.03582](https://arxiv.org/abs/2607.03582).
In particular, it solves the open
[Conjecture 5 entry in Google DeepMind's Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/b33d8678a28118c95d8d4f60b11faaf39ccff1e6/FormalConjectures/Arxiv/2607.03582/LpRogersShephard.lean)
and supplies the proved affirmative answer `answer(True)`.  Conjecture 4 is presented in the
same Formal Conjectures-facing format, including its unit-cube equality clause.

Try it in Lean4Web: [Open the standalone proof in Lean4Web](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Flp-rogers-shephard-conjectures-lean%2Frefs%2Fheads%2Fmain%2Flean4web%2FLpRogersShephardLean4WebAll.lean)

## Result

- **Conjecture 4:** proved in every positive dimension, including both the universal upper
  bound and the source paper's equality assertion for `K = [0,1]^n`.
- **Conjecture 5:** proved with the exact hypotheses, quantifier order, definitions, and
  conclusion of the current Formal Conjectures target.
- **Trust audit:** both final theorems use only Lean/mathlib's standard axioms
  `[propext, Classical.choice, Quot.sound]`; neither depends on `sorryAx`.

## Formal Conjectures-facing statements

```lean
/-- The unit cube `[0,1]^n` in the theorem's Euclidean-space model. -/
noncomputable def unitCube (n : ℕ) : Set (Ambient n) :=
  WithLp.ofLp ⁻¹' Set.Icc (0 : Fin n → ℝ) 1

/--
**Conjecture 4 (Fradelizi-Manui-Meyer-Ndiaye, 2026).** The symmetric-body
`L_p` Rogers--Shephard inequality in every positive dimension, with equality for the unit cube.
-/
@[category research solved, AMS 52]
theorem volume_lpSum_le :
    answer(True) ↔
      (∀ (n : ℕ), 1 ≤ n → ∀ (K : Set (Ambient n)),
        Convex ℝ K → IsCompact K → (interior K).Nonempty →
        HasCentreOfSymmetry K → (0 : Ambient n) ∈ K →
        ∀ p q : ℝ, 1 < p → 1 / p + 1 / q = 1 →
          volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant n q) * volume K) ∧
      (∀ (n : ℕ), 1 ≤ n → ∀ p q : ℝ, 1 < p → 1 / p + 1 / q = 1 →
        volume (lpSum p (unitCube n) (-(unitCube n))) =
          ENNReal.ofReal (rsConstant n q) * volume (unitCube n)) := by
  -- kernel-checked proof

/--
**Conjecture 5 (Fradelizi-Manui-Meyer-Ndiaye, 2026).** Among planar convex bodies with a
centre of symmetry containing the origin, for $p > 1$, equality in Corollary 29 holds only for
parallelograms with a vertex at the origin.
-/
@[category research solved, AMS 52]
theorem isParallelogramAtOrigin_of_volume_lpSum_eq :
    answer(True) ↔ ∀ (K : Set ℝ²), Convex ℝ K → IsCompact K → (interior K).Nonempty →
      HasCentreOfSymmetry K → (0 : ℝ²) ∈ K → ∀ p q : ℝ, 1 < p → 1 / p + 1 / q = 1 →
        volume (lpSum p K (-K)) = ENNReal.ofReal (rsConstant q) * volume K →
          IsParallelogramAtOrigin K := by
  -- kernel-checked proof
```

The source-facing declarations replace the unknown placeholder `answer(sorry)` by the proved
affirmative answer `answer(True)`.  The Conjecture 5 declaration uses the imported upstream
definitions directly, not merely isomorphic replacements.

## Mathematical Explanation (AI generated)

The Conjecture 4 upper-bound proof formalizes the centered-slice integral inequality and
evaluates its coefficient by the beta integral.  Its equality proof defines the unit cube as
the coordinate box `[0,1]^n`, proves that every weighted slice is the coordinate box

```text
[-t^(1/q), (1-t)^(1/q)]^n,
```

and proves the reverse inclusion in the fiber superlevel estimate.  Hence the layer-cake
inclusion used for the general upper bound is an equality for the cube.  The same beta-integral
evaluation then gives exactly `rsConstant n q * volume (unitCube n)`.

The Conjecture 5 equality proof follows the endpoint--fiber rigidity argument:

1. Lemma 5.3 gives the pointwise lower bound
   `1 - gauge D z ^ q ≤ fiberLength q K (-K) z`.
2. Equality of the total volumes, layer cake, and continuity force equality at every interior
   point of the parameter body.
3. A support point `u` in a direction orthogonal to the symmetry centre has the singleton
   fiber `{1/2}`.
4. For `0 < τ < 1`, the radial inclusion and the sharp fiber length give the exact fiber
   `[τ^q / 2, 1 - τ^q / 2]`.
5. Its two endpoints normalize to boundary points on `[-c,u]` and `[c,u]`. Continuity and
   central symmetry produce all four boundary segments.
6. Supporting functionals at two side midpoints trap the centered body in the quadrilateral
   `convexHull ℝ {c,u,-c,-u}`. Translating by `c` yields a parallelogram with a vertex at the
   origin.

The file also contains the intermediate theorem that sharp equality makes `0` an extreme
point of `K`.

## Files

| File | Purpose |
|---|---|
| `lean4web/LpRogersShephardLean4Web.lean` | Standalone mathlib-only definitions and exact targets |
| `lean4web/LpRogersShephardProof.lean` | Conjecture 4, Lemma 5.3, integral and coefficient calculations |
| `lean4web/LpRogersShephardEquality.lean` | Unit-cube equality for Conjecture 4 and the full Conjecture 5 equality-case proof |
| `lean4web/LpRogersShephardLean4WebAll.lean` | Single-file Lean4Web bundle containing both complete proofs |
| `lean/LpRogersShephardFC.lean` | Bridge to the pinned upstream Formal Conjectures definitions |

Both packages use Lean `v4.27.0` and mathlib `v4.27.0`. The Formal Conjectures package is
pinned to commit `b33d8678a28118c95d8d4f60b11faaf39ccff1e6`.

The mathlib-only development is also compatibility-tested against the public Lean4Web
`MathlibDemo` environment from 2026-08-14: Lean `v4.34.0-rc1`, mathlib commit
`4d476f6d4437a73c980a585e94a5030e3b51145b`.  To inspect both complete proofs with one
browser Load, use `LpRogersShephardLean4WebAll.lean`.  The shorter
`LpRogersShephardLean4Web.lean` contains only the standalone definitions and exact targets.

## Verification

Mathlib-only package:

```bash
cd lean4web
lake update
lake build
# Optional: compile the single-file browser bundle explicitly.
lake build LpRogersShephardLean4WebAll
```

Formal Conjectures bridge:

```bash
cd lean
lake update
lake build LpRogersShephardFC
```

Expected final audit:

```text
'LpRogersShephardLean4Web.conjecture4_full_proved' depends on axioms:
[propext, Classical.choice, Quot.sound]

'LpRogersShephardLean4Web.conjecture5_proved' depends on axioms:
[propext, Classical.choice, Quot.sound]

'LpRogersShephardFC.Conjecture4.volume_lpSum_le' depends on axioms:
[propext, Classical.choice, Quot.sound]

'LpRogersShephardFC.isParallelogramAtOrigin_of_volume_lpSum_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

## Appendix: Conjecture 4, from the paper to Lean

### Natural-language statement in the paper

[Conjecture 4 of the paper, p. 4](https://arxiv.org/pdf/2607.03582#page=5) is:

> [!IMPORTANT]
> **Conjecture 4 (Fradelizi--Manui--Meyer--Ndiaye, 2026).**
>
> Let $K \subset \mathbb{R}^n$ be a convex body that contains the origin and has a center of
> symmetry, and let $p>1$. Then
> $$
>   |K \oplus_p (-K)|
>   \leq \kappa^{(s)}_{n,p}|K|,
>   \qquad
>   \kappa^{(s)}_{n,p}
>   = \sum_{i=0}^{n}
>       \frac{\binom{n}{i}}{\binom{n/q}{i/q}}.
> $$
> Equality is attained when $K=[0,1]^n$.

The displayed wording of Conjecture 4 does not repeat the condition on $q$. It inherits the
paper's convention immediately preceding it: $q$ is the Hölder conjugate of $p$, so
$1/p+1/q=1$. A self-contained Lean theorem cannot leave that surrounding convention implicit,
which is why the formal statement quantifies over `q` and includes `1 / p + 1 / q = 1`.

The generalized binomial coefficient in this statement is

$$
  \binom{x}{y}
  = \frac{\Gamma(x+1)}{\Gamma(y+1)\Gamma(x-y+1)}.
$$

### Source-facing Lean statement

The final Conjecture 4 declaration in `lean/LpRogersShephardFC.lean` is:

```lean
theorem volume_lpSum_le :
    answer(True) ↔
      (∀ (n : ℕ), 1 ≤ n → ∀ (K : Set (Ambient n)),
        Convex ℝ K → IsCompact K → (interior K).Nonempty →
        HasCentreOfSymmetry K → (0 : Ambient n) ∈ K →
        ∀ p q : ℝ, 1 < p → 1 / p + 1 / q = 1 →
          volume (lpSum p K (-K)) ≤
            ENNReal.ofReal (rsConstant n q) * volume K) ∧
      (∀ (n : ℕ), 1 ≤ n → ∀ p q : ℝ, 1 < p → 1 / p + 1 / q = 1 →
        volume (lpSum p (unitCube n) (-(unitCube n))) =
          ENNReal.ofReal (rsConstant n q) * volume (unitCube n))
```

Its coefficient is defined by the same gamma-function formula:

```lean
noncomputable def generalizedBinomial (x y : ℝ) : ℝ :=
  Real.Gamma (x + 1) /
    (Real.Gamma (y + 1) * Real.Gamma (x - y + 1))

noncomputable def rsConstant (n : ℕ) (q : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    (Nat.choose n i : ℝ) /
      generalizedBinomial ((n : ℝ) / q) ((i : ℝ) / q)
```

### Term-by-term correspondence

| Paper | Lean | Why they agree |
|---|---|---|
| $n$ is a positive dimension | `n : ℕ`, `1 ≤ n` | `Ambient n` is the Euclidean space `EuclideanSpace ℝ (Fin n)`. |
| $K\subset\mathbb R^n$ is a convex body | `K : Set (Ambient n)`, `Convex ℝ K`, `IsCompact K`, `(interior K).Nonempty` | In the paper, “convex body” means convex, compact, and with nonempty interior. |
| $K$ contains the origin | `(0 : Ambient n) ∈ K` | This is the literal membership statement $0\in K$. |
| $K$ has a center of symmetry | `HasCentreOfSymmetry K` | This expands to invariance under `x ↦ 2 • c - x` for some center `c`. For a nonempty convex invariant set, that center lies in $K$, matching the paper's convention. |
| $p>1$ | `1 < p` | Literal translation. |
| $q$ is Hölder-conjugate to $p$ | `1 / p + 1 / q = 1` | This is the defining conjugacy equation used in the paper. |
| $K\oplus_p(-K)$ | `lpSum p K (-K)` | `lpSum` is defined by the Firey support-function identity, and `-K` is reflection through the origin. |
| $\lvert K\rvert$ and $\lvert K\oplus_p(-K)\rvert$ | `volume K` and `volume (lpSum p K (-K))` | `volume` is Lebesgue/Haar volume on the finite-dimensional Euclidean space. |
| $\kappa^{(s)}_{n,p}$ | `rsConstant n q` | Expanding `rsConstant` and `generalizedBinomial` gives exactly the paper's finite sum and gamma quotient. `Finset.range (n + 1)` is precisely $i=0,\ldots,n$. |
| $K=[0,1]^n$ | `unitCube n` | `unitCube n` is the preimage of the coordinate interval `Set.Icc 0 1` under the standard Euclidean-space equivalence. |
| Equality is attained by the unit cube | The second conjunct, with `=` | This is now a kernel-checked equality theorem, not only an example mentioned in prose. |
| The conjectured inequality is true | `answer(True)` | The formerly unknown proposition is answered affirmatively. |

Thus the two conjuncts of the Lean conclusion correspond exactly to the two mathematical
claims in the paper's boxed Conjecture 4: first the universal upper bound, then attainment of
that bound by `K=[0,1]^n`.  Internally they are proved separately as `conjecture4_proved` and
`conjecture4_unitCube_eq_proved`, and exported together as `conjecture4_full_proved`.

## References

- Matthieu Fradelizi, Auttawich Manui, Mark Meyer, and Cheikh Saliou Ndiaye,
  *$L_p$-Rogers--Shephard type inequalities for $L_p$-zonoids and symmetric bodies*,
  [arXiv:2607.03582](https://arxiv.org/abs/2607.03582), 2026.
- Google DeepMind, [Formal Conjectures: Planar $L_p$-Rogers--Shephard, the equality
  case](https://github.com/google-deepmind/formal-conjectures/blob/b33d8678a28118c95d8d4f60b11faaf39ccff1e6/FormalConjectures/Arxiv/2607.03582/LpRogersShephard.lean).

## AI usage disclosure

This formalization was developed with assistance from OpenAI Codex, using GPT-5.6 sol.
