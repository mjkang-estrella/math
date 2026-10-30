# Odd-unit midpoint primitives — closed component

All six mandatory requirements are complete in four new Lean modules. Import
`OddPrimitiveSequence`; the new namespace is `JacobiShifted.MidpointRational`.
This is solely the midpoint odd-primitive component. Root alone integrates it.
No source-level Jacobi denominator theorem or discovery acceptance is asserted.

## Frozen inputs

`BinaryDigits`, `Filtration`, `Riccati`, `NonSubring`, `MidpointAlgebra`,
`MidpointSequence`, `MidpointParity`, and `MidpointNormalForm` are copied
byte-identically from the root sources identified by the user as frozen at
`ebae06005b388f3aba769133ad8b413b78c93b86`. They were not edited. Their hashes
match the root integration maps. `FiltrationAudit`, `MidpointAudit`, and the
root `run_lean.py` are also copied byte-identically; `guard.py` is copied
byte-identically from the completed midpoint lane. See `copy-verification.json`.
No git command was used to inspect or modify a repository. The association
with the frozen commit is the supplied root provenance, independently checked
here against the completed integration hash maps and working source bytes.

The supplied ordinary proof hash was verified:
`e086fe86d3dea5c2931793b5bf8eb63c26509805d7a2b15808f6abac2763d191`.
Its Sections 1–4, preliminary review Section 3, root midpoint integration note
and import map, and the completed midpoint worker summary were read.

## Rational algebra and embedding

`MidpointRational.lean` defines the actual pair algebra

```lean
QPoly := Polynomial ℚ
q := 1 + Polynomial.X^2
QAlg := QuadraticAlgebra QPoly q 0
```

`C`, `x`, `w`, `delta`, `flip`, `tau`, and `midpoint` are concrete maps and
objects. `delta` is an additive map and a proved derivation; `tau` is a ring
involution; `midpoint : QAlg →+* ℚ` evaluates `x=0,w=1`.

| Exact interface | Proved content |
|---|---|
| `pair_mul`, `pair_normal`, `w_sq` | Genuine pair multiplication and `w²=1+x²`. |
| `partial_re`, `partial_im`, `partial_mul` | Real coordinate `-q*r'`, imaginary coordinate `-X*g-q*g'`, and Leibniz. |
| `tau_x`, `tau_w`, `tau_involution`, `tau_partial` | `x,w ↦ -x,-w`; involution and anticommutation with `delta`. |
| `zmap`, `zmap_coeff`, `zmap_comp`, `zmap_derivative`, `zmap_injective` | Actual coefficient map `ℤ[X] → ℚ[X]`, with injectivity and polynomial compatibility. |
| `lift : Midpoint.R →+* QAlg` | Pairwise application of `zmap`; it is an actual ring homomorphism. |
| `lift_re`, `lift_im`, `lift_x`, `lift_w`, `lift_C` | Explicit coordinate and generator formulas. |
| `lift_injective`, `lift_delta`, `lift_tau`, `lift_midpoint` | Injectivity and compatibility with all three integer midpoint maps. |

The extra rational `rho` and generator identities are also proved and audited.
No Laurent embedding is assumed or used.

## Literal triangular inversion and local arithmetic

`OddTriangular.lean` defines

```lean
T f := f + 2*(1+Polynomial.X)*Polynomial.derivative f
TwoLocal a := Odd a.den
```

`twoLocal_iff_odd_den` states the exact equivalence explicitly; this predicate
is definitionally the same odd-denominator predicate used by the root source
module. `twoLocal_add`, `twoLocal_sub`, `twoLocal_neg`, `twoLocal_mul`,
`twoLocal_int`, `twoLocal_nat`, and `twoLocal_div_odd_nat` establish the actual
local arithmetic. Odd division is justified by reduced-denominator divisibility,
not by rational divisibility.

`T_coeff f k` proves the precise triangular identity

```text
(T f)_k = (2k+1) f_k + 2(k+1) f_(k+1).
```

`Bounded N f` means every coefficient at index at least `N` is zero.
`finiteDegree N : Submodule ℚ QPoly` is the actual submodule of degree less
than `N`, including zero. `T_surjective_bounded` reconstructs a polynomial
solution of `T f=B` inside that submodule: at each finite step it subtracts
`T(C(B_N/(2N+1))*X^N)`, solves the strictly smaller problem, and adds the
monomial back. The base submodule `N=0` is handled explicitly.

`T_kernel` uses the nonzero top diagonal to prove the kernel is zero.
`T_bijective` and `T_finiteDegree_bijective N` prove global and every
finite-degree bijection. Only after this existence proof is `inverseT`
selected with `Classical.choose`. `T_inverseT`, `inverseT_T`,
`inverseT_unique`, `inverseT_add`, `inverseT_smul`, and `inverseT_bounded`
prove its literal equation, uniqueness, linearity, and degree preservation.
There is no assumed inverse or coefficient-sequence surrogate.

The key generic arithmetic theorem is

```lean
T_twoLocal {f B : QPoly} (e : ℕ) (he : T f = B)
  (hB : ∀ k, TwoLocal (B.coeff k / (2 : ℚ)^e)) :
  ∀ k, TwoLocal (f.coeff k / (2 : ℚ)^e)
```

It descends from the vanishing coefficient beyond `f.natDegree`. The identity
expresses `f_k/2^e` as the difference of the known localized terms divided by
the odd natural `2k+1`. All coefficients outside that finite range are zero.
`inverseT_twoLocal` specializes it to the proved inverse for every `B,e`,
including the zero polynomial. Its hypothesis concerns only `B`.

## Genuine normalized primitives and midpoint estimate

`MidpointPrimitive.lean` defines the finite polynomial

```text
realIntegral A = -Σ(k∈support A) C(A_k/(2k+1))*X^(2k+1).
```

`derivative_realIntegral`, `delta_realIntegral`, `flip_realIntegral`, and
`realIntegral_zero_eval` prove its differential identity, tau parity, and
vanishing at zero. `delta_quadratic` and `delta_quadratic_expanded` prove

```text
δ(w*C(f(X²))) = -w*x*C((T f)(X²))
             = -w*x*C(f(X²)+2(1+X²)f'(X²)).
```

For any integral `A B`, the actual element is

```lean
primitive A B :=
  C (realIntegral (zmap A)) +
  w*C ((inverseT (-zmap B)).comp (Polynomial.X^2))
```

`primitive_delta` proves its derivative is
`lift (Midpoint.normalForm A B)`. `primitive_tau` proves it is tau-odd.
`primitive_midpoint` identifies its midpoint with
`(inverseT (-zmap B)).coeff 0`; the real primitive contributes exactly zero.

`zmap_twoLocal_of_dvd` transfers genuine integral polynomial divisibility
`(2:ℤ[X])^e ∣ B` to coefficient localization after division by `2^e`.
`primitive_midpoint_twoLocal A B e hB` then proves

```lean
TwoLocal (midpoint (primitive A B) / (2 : ℚ)^e)
```

There is no divisibility hypothesis on `A`.

`imaginary_kernel` proves `X*g+(1+X²)g'=0 → g=0` by taking the coefficient at
`natDegree(g)+1`; its nonzero multiplier is `natDegree(g)+1`.
`delta_kernel p` proves the full equivalence

```lean
delta p=0 ↔ ∃ a : ℚ, p=C (Polynomial.C a)
```

`normalized_kernel` eliminates that constant by tau-oddness.
`normalized_unique` identifies any two tau-odd primitives with equal
actual derivatives. `primitive_unique` and
`normalForm_primitive_existsUnique` finish the normal-form result.
Thus the primitive has a proved normalization and can be identified by
uniqueness without any Laurent argument or integration-constant premise.

## Closed instantiation of the existing concrete sequence

`OddPrimitiveSequence.lean` imports and uses the unchanged concrete `Midpoint.h`.
`h_extracted_divisible n i j` uses `h_odd_extraction_divisible` for odd `j`,
and `h_even_j_im_zero` plus `oddExtract_zero` for even `j`.
`h_odd_primitive_existsUnique` proves, for all naturals `n i j` and `Odd n`,

```lean
∃! p : QAlg,
  delta p = lift ((Midpoint.h n).coeff (bidegree i j)) ∧ tau p = -p
```

The identification-ready arithmetic interface is

```lean
h_odd_primitive_midpoint (n i j : ℕ) (hn : Odd n) (p : QAlg)
  (hd : delta p = lift ((Midpoint.h n).coeff (bidegree i j)))
  (ht : tau p = -p) :
  TwoLocal (midpoint p / (2 : ℚ)^sigma (i+j-1))
```

It applies to **any** primitive whose actual derivative and normalization
are proved. The existence theorem above supplies those objects internally;
there is no unexplained selection premise. `h_odd_primitive_closed` combines
existence, uniqueness, and this bound in a single closed theorem.
`h_odd_primitive_midpoint_even` proves midpoint exactly zero for even `j`.

All bidegrees are included. `h_zero_parameter` derives the actual zero
parameter coefficient from the proved `h_weighted`; `h_zero_parameter_primitive`
proves any normalized primitive of that coefficient is zero. No positive
parameter-degree or degree-support condition is hidden in these endpoints.

## Strict replay and exhaustive audits

The fresh source-only replay succeeded in `verification/fresh/`, starting
with zero local oleans. All twelve proof builds have empty logs. Both frozen
dependency audits and both new audits passed. The pinned Lean binary SHA and
mathlib revision were checked before building. Commands are sequential with
`-j1 -M4096`, `warningAsError=true`, `autoImplicit=false`. The supplied guard
samples the runner/Lean process-tree RSS every 0.2 seconds, kills above 3 GiB,
and applies no virtual-memory cap. Sampled replay peak: **2,745,208 KiB**.

`OddPrimitiveInventory` selects declarations by their actual source-module
origin, not merely their name prefix. It covers all **193** declarations
introduced by the four new proof modules: **140** explicit declarations and
**53** compiler auxiliaries. Every safety flag is false. Every declaration
has an actual `#check` and `#print axioms` report; all depend only on
`propext`, `Classical.choice`, and `Quot.sound`, or fewer. I read all actual
new type/axiom reports. The fresh new audit reproduces the development audit
byte-for-byte. Its complete output is
`verification/fresh/logs/13-OddPrimitiveAudit.log`.

The frozen `MidpointAudit` and `FiltrationAudit` also report the permitted
axioms for all their 186 and 54 declarations. The source inventory, safety
report, full commands, source hashes, resource samples, and parsed audit
coverage are in `verification/fresh/receipt.json` and adjacent logs.
`OddPrimitiveInventory` is audit tooling, outside the four mathematical
modules whose full environment it inventories. Only its intentional compiler
auxiliary references disable the auxiliary style linter in the axiom audit;
warnings remain errors everywhere.

Reproduce from this lane with a new, nonexistent output directory:

```bash
python3 replay.py --output verification/root-replay
```

`formal-source.tar.gz` contains only sources and runner scripts, with no
prebuilt local oleans. Archive SHA-256:
`3a66d345873c15c59087e9820db310816149a5ea2095462a2d6403e565c01262`.
`source-manifest.json` hashes every archived file. `provenance.json` records
inputs, pins, exact new-module hashes, and report hashes. All corrected
development failures and resources are retained in
`RESOURCE-AND-FAILURE-LOG.md` and `verification/development/`.

## Remaining scope and limits

There are no known gaps in the six mandatory items assigned to this lane.
Source/logarithm identification, parameter-degree support, Laurent embedding
and coordinate scaling, Catalan source coefficients, and final source assembly
remain outside this component. No coefficientwise Laurent-primitive dyadic
bound is claimed. Only the normal-form midpoint estimate is proved here.
The optional coefficientwise localization theorem for the whole primitive
was not needed or added; the generic inverse coefficient theorem is proved.

All writes stayed in the assigned lane. No children, other-lane/shared edits,
git commands, manuscript, external communication, account action, posting,
or browser tab was used. This is implementation and solo verification;
root's integration and any independent review remain root responsibilities.
