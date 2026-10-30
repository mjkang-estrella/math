# discovery.md — mathematical content of the lane (verification of a public resolution, not a new result)

Date: 2026-10-28. Everything below was re-derived independently in this lane from the
statement of Karp arXiv:1509.05120v1 Conjecture 2; it then turned out to coincide (step for
step) with the public Lean route at trureturing commit 337295b. It is recorded here because
it is the verification basis for declaring the target resolved, and because it documents why
the generic routes tried by earlier root lanes had to fail.

## 1. Reduction to a sliding-window statement

Let `h=h_b`, `T=2a+alpha+beta`, `S=T+k`, and

    A(x) = sum_{s=0}^k h(x+s) h(S-x-s) = sum_{s=0}^k r_S(x+s),  r_S(u)=h(u)h(S-u).

Then `psi_k = A(a+alpha) - A(a)`; `A(x)=A(T-x)`. WLOG `alpha<=beta` (swap), so the conjecture
(b>1 half) is equivalent to: `A` is nondecreasing on `x in (0, T/2] = (0,(S-k)/2]`, i.e.

    (L)  sum_{s=0}^k r_S'(x+s) >= 0 for 0 < x <= (S-k)/2, all S>k>=0.

This equivalence is what made the problem look approachable by pure log-concavity; the r17
counterexample (`h=t^2`) shows (L) fails for general positive increasing log-concave `h`,
because then `r'` vanishes at the domain boundary and is not monotone in distance from the
symmetry center. The pairwise sufficient condition "`r_S'` nonincreasing on `(0,S/2)`" is
also false even for `h_3` (S=10: r'(0)=175 < r'(0.1)=181.04), so no purely local argument of
this shape can work. The Gamma ratio needs its exact mixture structure.

## 2. The structure that works: shifted-beta mixture (verified by hand)

Write `c_j(t,b)=h_b(t+j)` and `S_n(p,q;b)=sum_{k=0}^n c_k(p,b)c_{n-k}(q,b)`, so
`psi_n = S_n(a+alpha,a+beta;b) - S_n(a,a+alpha+beta;b)`.

(a) *Termwise beta integration.* For `b>1`, with `m=b-1>0`,
`c_j(p,b) = Gamma(b-1)/(Gamma(b) B(p+j+1,b-1))`, hence

    S_n(p,q;b) = (1/(b-1)^2) sum_k Gamma(p+b+k)Gamma(q+b+n-k) / (Gamma(p+k+1)Gamma(q+n-k+1)).

(b) *Affine mixture identity (re-derived exactly).* Define the uniform mixture

    rho(y) = (1/(n+1)) sum_{k=0}^n y^(p+k)(1-y)^(q+n-k) / B(p+k+1,q+n-k+1).

Claim: `rho` is the density of `Y=sV+(1-s)U`, `s~Beta(p+q,n+2)`, `V~Beta(p,q)`, `U~U(0,1)`
independent. Proof: the map `(v,s) -> (x,z)=(sv,s(1-v))` has Jacobian `s`; at fixed output
`y` the domain is `0<x<y, 0<z<1-y`; the pushed density is

    rho(y) = 1/(B(p+q,n+2)B(p,q)) int_0^y int_0^{1-y} x^(p-1) z^(q-1) (1-x-z)^n dx dz

(the `(x+z)` powers cancel exactly because `c=p+q`), and expanding
`(1-x-z)^n = ((y-x)+(1-y-z))^n` binomially gives term `k` equal to
`y^(p+k)(1-y)^(q+n-k) Gamma(p+q+n+2)/((n+1) Gamma(p+k+1) Gamma(q+n-k+1))` — exactly `rho`.

(c) *Kernel identity.* With `w_b(y)=[y(1-y)]^(b-1)`,

    S_n(p,q;b) = K(c,n,b) * int_0^1 w_b(y) rho(y) dy,  K(c,n,b) = (n+1)Gamma(c+n+2b)/(Gamma(b)^2 Gamma(c+n+2)),

obtained by integrating `w_b * rho` termwise (`int y^(p+k+b-1)(1-y)^(q+n-k+b-1) =
B(p+k+b,q+n-k+b)`). Hand-checked: `b=2, n=0` gives `S_0=(p+1)(q+1)` both ways.

(d) *Kernel monotonicity.* `F_s(v)=int_0^1 w_b(sv+(1-s)u)du = (1/(1-s))int_{sv}^{sv+1-s} w_b`
so `F_s'(v) = (s/(1-s))[w_b(sv+1-s)-w_b(sv)]`. For `v<1/2`, with `l=sv, r=sv+1-s`:
`l+r = 1-s(1-2v) < 1` and `l<r`, which forces `min(r,1-r) > min(l,1-l)`; since `w_b` is
symmetric about 1/2 and (for b>1) strictly increasing on (0,1/2), `F_s'(v)>0`. Also
`F_s(1-v)=F_s(v)` (substitute `u -> 1-u` and use symmetry of `w_b`). Hence

    H(c,n,b)(v) := Beta(c,n+2)-average of F_s(v)

is symmetric about 1/2, bounded, continuous, strictly increasing on `(0,1/2]` for `b>1`
(strictly decreasing for `0<b<1`, where `w_b` flips).

(e) *Conclusion.* By (b)-(c), `S_n(p,q;b) = K * betaMean(H; (p+q)/2, (p-q)/2)`. At fixed sum
`p+q` the beta mean of a bounded symmetric function strictly increasing toward 1/2 is
strictly decreasing in `|p-q|` (standard crossing comparison, Lean-proved in the registry's
sibling Conjecture-1 module as `betaMean_strictAntiOn`). The pairs `(a+alpha,a+beta)` and
`(a,a+alpha+beta)` have the same sum `2a+alpha+beta` and imbalances `|alpha-beta|/2 <
(alpha+beta)/2`. Hence `S_n(a+alpha,a+beta;b) > S_n(a,a+alpha+beta;b)` for `b>1` and the
reverse for `0<b<1`: exactly Conjecture 2, both branches, all real shifts.

## 3. Why this is not creditable

The route above is published, complete and machine-checked at
`D5/S3.Analytic.IncompleteBetaShape.Result.result` (commit 337295b, 2026-10-28T16:10:44Z),
with definitions literally matching the source (`coeff` = `h_b(t+j)`, no `k!` weight, all
real parameters, both signs). Under the batch rules a public proof excludes credit, and any
Lean endpoint built now would formalize a known public theorem. The lane therefore stops
here; see SUMMARY.md.

## 4. Relation to earlier root lanes

- `root-beta-convolution-r9` (1<b<=2 via strict Jensen concavity) and the r6 CM-series
  observation (0<b<1) are sub-cases of (e); both were already uncredited.
- `root-beta-convolution-r17`'s generic-route counterexample is consistent: (e) uses the
  exact mixture structure of the Gamma-ratio lattice samples, which `h=t^2` lacks; no
  generic discrete-convolution-unimodality theorem is implied by the public proof.
- The b=3 exact all-k/all-real-shift identity of r17 is an instance of (e) at `b=3`.
