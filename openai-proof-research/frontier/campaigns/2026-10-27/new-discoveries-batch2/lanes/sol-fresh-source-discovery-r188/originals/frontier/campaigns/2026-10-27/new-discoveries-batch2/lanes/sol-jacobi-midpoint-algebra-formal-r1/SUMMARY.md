# Concrete integral midpoint component — complete

Mandatory items 1–5 are proved in the four new Lean modules under `formal/`.
This is a closed component for the shifted-variable Jacobi denominator
formalization. It is not a literal source theorem, an independent final review,
or a discovery-acceptance claim.

All new mathematics is in `JacobiShifted.Midpoint`. Root can import
`MidpointNormalForm`; it transitively imports the other three new modules and
the unchanged integrated binary-filtration modules. Root alone integrates.

## Exact algebra and maps

`ZPoly := Polynomial ℤ`, `q := 1 + Polynomial.X^2`, and
`R := QuadraticAlgebra ZPoly q 0`. These are actual integral polynomial pairs.
`C : ZPoly →+* R`, `x = ⟨X,0⟩`, and `w = ⟨0,1⟩` are concrete definitions.

| Interface | Proved content |
|---|---|
| `pair_eq_iff`, `pair_mul`, `pair_normal`, `w_mul_pair` | Coordinate uniqueness and actual pair arithmetic; every `z` equals `C z.re + w*C z.im`. |
| `w_sq` | `w^2 = 1+x^2`. |
| `delta : R →+ R` | Real coordinate `-q * derivative z.re`; imaginary coordinate `-X*z.im - q*derivative z.im`. |
| `partial_mul`, `partial_x`, `partial_w` | Leibniz and the exact generator formulas for `delta`, the operator ∂. |
| `derivation : Derivation ℤ R R`, `derivation_apply` | The same operator bundled as a genuine integer derivation. |
| `rho`, `rhoEquiv`, `rho_involution`, `rho_x`, `rho_w`, `rho_partial` | Ring reflection `x ↦ x`, `w ↦ -w`; involutive and commuting with ∂. |
| `flip`, `flip_apply`, `tau`, `tauEquiv`, `tau_involution`, `tau_x`, `tau_w`, `tau_partial` | Polynomial substitution `X ↦ -X` and the ring involution `x,w ↦ -x,-w`; ∂ anticommutes with `tau`. |
| `midpoint`, `midpoint_apply`, `midpoint_x`, `midpoint_w`, `midpoint_C` | Ring homomorphism `R →+* ℤ`, `z ↦ z.re.eval 0 + z.im.eval 0`, with `x ↦ 0`, `w ↦ 1`. |

No relation-preservation or derivation-preservation hypothesis is used.

## Constructed sequence and closed integral filtration

`P : MvPolynomial (Fin 2) R` is literally
`BinaryFiltration.initial (w^2) (w*x)`. `history` uses only primitive `Nat.rec`
to construct each finite prefix. `h n := history n (Fin.last n)`, and
`history_agrees` proves consistency of every earlier prefix entry.
The final implementation has no generated unsafe runtime declaration.

`h_zero`, `h_one`, and `h_recurrence` prove

```text
h 0 = 0,  h 1 = P,
h (n+1) = -coefficientOperator delta (h n)
          - ∑ i ∈ Finset.range (n+1), h i * h (n-i)     (1 ≤ n).
```

The two main arithmetic interfaces have no sequence-existence, closure,
operator-preservation, or recurrence premise:

```lean
h_weighted (n : ℕ) : BinaryFiltration.Weighted (h n)

h_odd_coefficient_divisible (n i j d : ℕ) (hj : Odd j) (hd : d=i+j) :
  (2 : R)^BinaryFiltration.sigma (d-1) ∣
    (h n).coeff (BinaryFiltration.bidegree i j)
```

They instantiate the unchanged `riccati_initial_weighted` and
`riccati_degree_odd_coefficient` with the actual constructed sequence and
proved recurrence. `h_weighted` also proves the zero parameter-constant term.
All divisibility is in the integral ring `R`.

## Independent coefficient parities and the integral ideal

`h_rho_coefficient n i j` proves
`rho z = (-1)^j*z`, with `z = (h n).coeff (bidegree i j)`.
`h_tau_coefficient n α` independently proves
`tau ((h n).coeff α) = (-1)^(n+1)*(h n).coeff α`.
Both hold for every natural index, including the stipulated zero term.
The proofs use actual coefficient convolution; no parameter swap is used.

`h_even_j_im_zero` and `h_odd_j_re_zero` extract the respective zero normal
components using coefficientwise integer cancellation.
`h_odd_order_coordinates` proves that for odd `n`, the real polynomial is
fixed by `flip` and the imaginary polynomial is negated by `flip`.

`InW z := ∃ y, z=w*y`; `inW_iff` proves `InW z ↔ q ∣ z.re` using actual
pair multiplication. `inW_ideal_span` identifies it with membership in
`Ideal.span {w}`. `inW_partial` proves preservation under ∂.
`h_wCoefficients`, `h_coefficient_re_divisible`, and `h_coefficient_mem_w`
prove all three versions for every actual parameter coefficient of every `h n`.

## Normal form and the primitive-worker interface

The extraction operators are actual finite integral polynomials:

```text
evenExtract p = Polynomial.contract 2 p
oddExtract p  = Polynomial.contract 2 p.divX
(evenExtract p).coeff k = p.coeff (2*k)
(oddExtract p).coeff k  = p.coeff (2*k+1).
```

`evenExtract_spec` and `oddExtract_spec` reconstruct even and odd polynomials
as `A.comp (X^2)` and `X*B.comp (X^2)`, respectively.
`even_quotient` proves from `flip p=p` and `p=q*a` that `flip a=a` by
cancelling the nonzero polynomial `q` in the domain `ℤ[X]`.
This parity of the quotient is derived, not assumed.

`normalForm A B` is the concrete pair
`⟨q*A.comp (X^2), X*B.comp (X^2)⟩`.
`normalForm_ring` identifies it with

```text
(1+x^2)*C (A.comp (X^2)) + w*x*C (B.comp (X^2)).
```

The closed theorem `h_odd_normalForm n i j (hn : Odd n)` supplies integral
`A B` satisfying this normal form, the formula
`B.coeff k = z.im.coeff (2*k+1)`, the bound
`(2:ℤ)^sigma(i+j-1) ∣ B.coeff k` when `j` is odd, and the additional
identifications `B=0` for even `j` and `A=0` for odd `j`.

For convenient downstream use, `h_odd_normalForm_ring` gives the ring
expression directly with canonical `B = oddExtract z.im`.
`h_odd_extraction_divisible n i j (hj : Odd j)` proves the stronger
polynomial divisibility statement

```lean
(2 : ZPoly)^BinaryFiltration.sigma (i+j-1) ∣
  oddExtract ((h n).coeff (BinaryFiltration.bidegree i j)).im
```

This last theorem does not even require `n` odd; oddness of `n` is needed to
reconstruct the normal form. `integral_im_coeff_divisible` and
`oddExtract_preserves_divisibility` prove the transfer from divisibility in
`R` to integer coefficients explicitly, using the actual algebra embedding,
constant-polynomial divisibility, and the displayed extraction formula.
There is no localization, rationalization, or assumed divisibility-preserving
extraction in this component.

## Replay and actual audits

The source-only packet is `formal-source.tar.gz`, SHA-256
`ad87077c0c334458654753a511d0dcd6d09f39341268d25c8f4670555117e5d7`.
`source-manifest.json` hashes every packaged file. Four reused proof modules,
the dependency audit, and both supplied runner scripts are verified
byte-identical in `copy-verification.json`.

Fresh replay succeeded in `verification/fresh/`, starting with zero local
oleans and using only the pinned upstream package builds. All eight proof
module logs are empty. The complete actual reports are:

- `verification/fresh/logs/09-MidpointAudit.log`: every new declaration's
  `#check` and `#print axioms` output, including generated auxiliaries.
- `verification/fresh/logs/10-FiltrationAudit.log`: the unchanged dependency
  audit's complete actual output.
- `verification/fresh/logs/11-Inventory.log`: exhaustive new environment
  inventory and safety flags.
- `verification/fresh/receipt.json`: build commands, exits, sampled resources,
  axiom parsing, coverage, source hashes and safety verification.

I read all actual type and axiom reports myself. The new audit covers 132
explicit declarations and 54 generated auxiliaries; every one is safe and
uses only `propext`, `Classical.choice`, and `Quot.sound` (some use fewer).
The dependency audit covers its 54 declarations, including the axiom-free
`additive_nat_mul`. The declaration inventory is `declarations.json`.
The audit disables only the auxiliary-reference style linter because it
intentionally audits frozen compiler auxiliaries. Warnings remain errors.

Run from this lane, choosing a new, nonexistent output directory:

```bash
python3 replay.py --output verification/root-replay
```

The script packages the exact current sources, extracts them, asserts zero
initial local oleans, verifies the pinned Lean binary hash and mathlib HEAD,
then builds sequentially with `-j1 -M4096`, `warningAsError=true`, and
`autoImplicit=false`. The supplied guard samples aggregate runner/Lean RSS
every 0.2 seconds and stops a build above 3 GiB. No virtual-memory cap is set.
Full resources and corrected development failures are in
`RESOURCE-AND-FAILURE-LOG.md` and `verification/development/`.

## Remaining work and scope

There are no known gaps in mandatory items 1–5 of this assigned component.
The optional full parameter-degree support bound was not separately proved;
its zero-constant part is already provided by `h_weighted`. The optional
rational Laurent embedding/injectivity and `D=2∂` were not attempted.

The source/logarithm bridge, coordinate scaling, odd-unit primitive theorem,
full source endpoint, paper, independent final review and acceptance remain
outside this component. No source theorem or discovery acceptance is claimed.
All writes stayed inside this lane. No git command, children, shared/candidate
edit, external communication, account action or browser tab was used.

Input hashes, exact pins and provenance are in `provenance.json`.
