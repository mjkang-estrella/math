# I345 proof review: source map and exact interfaces

2026-10-14. This map records each dependency of the I345 proof, with the exact statement used and where the review checks it ([review.md](review.md)). Pinned truth is stipulated at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` (sources/upstream.json, SHA-256 3784eb61…5f30c).

## Pinned OpenAI manuscript

The prefix is `preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/`.

On 2026-10-14 the reviewer fetched every file below from `https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/<prefix><file>`. The live SHA-256 of each matched both the I345 authentication record and the local corpus copy under `frontier/sources/i14_spectral_width_novelty_r3/corpus/`.

| File | SHA-256 | Reviewer reading |
|---|---|---|
| 01-introduction.tex | 8ee40e983c95205a700548341f97981b2c853bd9c483ebafd41aeff7a1e73884 | complete |
| 02-flatness.tex | c7711073ba1bcbf32daf063e4070c7b29f032d91bf0d4c96a7a4400622542a76 | complete |
| 03-reduction.tex | 50521fb6e7492fb3e866ca76d603200fa085b2159ada9d5a331361d47abf96eb | complete (377 lines) |
| 04-limiting-tools.tex | 1b604397b3b347b9fd3e8ad6c946cffa8d2714094e15e61ce1065874f80f004e | hash only; used only through I236 |
| 05-envelope-contact.tex | 1fc42a48767b53a3f93fe874b34ade9f2528d24ced9c0c6192bfea86ff7577d8 | hash only; used only through I236 |
| 06–08 (.tex) | 0bd74d9f…, b068ac40…, b7bcfc6e… | hash only; these lie inside the stipulated proof of thm:liouville |

### Exact pinned interfaces used

- **`thm:main`** (01): for d≥3 there exist α_d∈(0,1/3] and C_d such that every bounded infinity-harmonic u∈C(B1)⊂R^d satisfies ||∇u||_{L∞(B1/2)}+[∇u]_{C^{0,α_d}(B1/2)}≤C_d osc_{B1}u. Infinity-harmonic means viscosity sense, with all tests including those at zero gradient.
  - Used in I345 §2.3 for the entire Lipschitz infinity limit, after lifting to dimension n+1≥3 and scaling. Review section C.
- **`lem:linear-lift`** (02): if u is infinity-harmonic in Ω⊆R^d, then u(y)+b is infinity-harmonic in Ω×R, in any dimension d.
  - Used in I345 §2.3 only, for the exact infinity limit f. It is not applied to p-solutions. Review C.
- **`thm:liouville`** (03, lines 5–17): let m≥1 and C0<∞. If v∈C(R^m×R) is a viscosity solution of D²v[(∇_xv,1)]=0 and has, at every center and every R, a fit (p,a) with |v(x+h,t+ℓ)−v(x,t)−p·h−(a−|p|²/2)ℓ|≤C0R whenever |ℓ|≤R and |h−pℓ|≤R, then v is affine.
  - Used in I345 §6 at ν=0, both for V itself and for the projected W with m=n−1≥1. Review H.
- **`lem:bad-scales`** (03, lines 128–156): equation-free; reused with the strengthening "approximate maximum ≥ i". Review E.
- **`lem:cylinder-comparison`** (03, lines 160–181): **equal parameter θ²** and slopes in [c_*,C_*]. Same center with H≤H'≤2H gives |P−P'|+|n−n'|≤Cθ and ||P|−|P'||≤Cθ². The displaced-center variant needs quarter margins.
  - Used for the equal-η chain in I345 §8.1. It is **not** applicable to the Λλ-versus-η pair; that gap is the I344 defect, repaired in Review J.
- **`lem:family-flatness`, slope bounds (eq:physical-slope-bounds)** (03, lines 56–69): |P|≤L+√λ and |P·e_b−1|≤√λ. Equation-free. Review E and J.
- **`prop:nonaffine-limit`** (03, lines 210–301): the geometric part only, which is everything except line 282's PDE identification. That line is replaced by I345 §5–6. Review F.
- **Gradient extraction** (03, lines 311–375): equation-free. Review M.

The three-point estimate `prop:three-point` (02) is **not** used for p-solutions. I345 replaces it with expanding-domain rigidity, and I confirmed this.

## Internal input

- **I236** `frontier/experiments/i236_viscous_contact_propagation/analytic-attempt.md`, SHA a30077ca36f40e6613e340d3f8ae0ac692000f7b39d6eb4113897f40b7c68931. The reviewer read it completely.
  - Interface: for every m≥1, 0<τ<∞ and C0<∞, every continuous entire viscosity solution of D²V[(D_xV,1)]+τΔ_xV=0 with the same all-center, all-radius sheared FIT is affine. No other regularity is assumed.
  - Status: proof PASS by I239, as recorded in `frontier/iterations/i239-viscous-proof-parent-disposition.md` (SHA bf335a6f…). Contribution was judged TECHNICAL by I240, which is irrelevant to this proof dependency.
  - Used in I345 §6 at ν>0. Review L, with R3 required.
- **I344** route (SHA ba36168c…, matches the prescribed hash). This is the source of the carried objection. Review J.
- **Parent note** `campaigns/2026-10-14/p-gradient-parent/ellipticity.md` (SHA f4ea3e49…): explicit M0 bounds (b0²/3)|·|²≤M0≤2|·|². Consistent with the reviewer's exact Schur-complement check.

## Classical external interfaces

| Source | Exact interface used | Reviewer reading | Review |
|---|---|---|---|
| Kotschwar–Ni, arXiv:0711.2291v1, Thm 1.1 | quoted verbatim in review A (positive p-harmonic v on B(x0,R), K_M≥−K², any ε∈(0,1), u=−(p−1)log v) | theorem statement and constants read from the arXiv HTML on 2026-10-14; the proof was not re-read | A |
| Savin, CPDE 32 (2007) 557–578, H1–H4, Thm 1.3, Prop 4.1 | small-solution C^{2,α} for F elliptic, uniformly elliptic with C² bounds near zero jets, F(0,0,0,x)=0; Prop 4.1 is a sequence argument with \|\|D²F_k\|\|≤K and r0=r0(δ,K,universal) | local extraction pp. 1–4 and 14–18 (SHAs c2e5fcf4…, be8cae92…); pp. 5–13 not read (U3) | I |
| Uhlenbeck, Acta Math. 138 (1977); or another compact-p C^{1,θ} source | uniform C^{1,θ} and fixed-p Liouville for p∈[3,P] | not re-read by the reviewer (U1); citation repair R1 | B |
| Julin–Juutinen arXiv:1104.2197; Juutinen–Lindqvist–Manfredi | weak solutions of the p-Laplacian ⇔ viscosity solutions (p≥2, all tests) | not re-read by the reviewer (U4) | C, D |
| Crescimbeni–Forzani–Perini (EJDE 2007) | linear divergence-form Harnack inequality | only through I236/I239 | L |
