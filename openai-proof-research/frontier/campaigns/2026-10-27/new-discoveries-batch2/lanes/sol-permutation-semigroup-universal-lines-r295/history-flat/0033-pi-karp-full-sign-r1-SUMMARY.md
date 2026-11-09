# pi-karp-full-sign-r1: Karp Conjecture 2 (MathDB 331384) is publicly RESOLVED — credit 0, no discovery

28 October 2026. Lane outcome: **the full source target is no longer open**, so this lane
produces no discovery, no formalization, no paper, no packet, and **credit 0**. The additional
tally is unchanged (2/30 per ledger).

## What the target was

D. B. Karp, arXiv:1509.05120v1, Section 3, Conjecture 2 (MathDB 331384, status open,
solutions array empty): with `h_b(t)=Gamma(t+b)/(Gamma(t+1)Gamma(b))` and

    psi_k = sum_(i=0)^k [h_b(a+alpha+i) h_b(a+beta+k-i) - h_b(a+i) h_b(a+alpha+beta+k-i)],

all `a,alpha,beta>0`, `k>=0`: `psi_k<0` for `0<b<1` and `psi_k>0` for `b>1`. The source's own
Corollary 1 already proves the whole `0<b<1` half and the integer-shift `alpha in N`,
`beta>=alpha-1` case; root lanes `root-beta-convolution-r9` (1<b<=2) and
`root-beta-convolution-r17` (exact b=3 all-k/all-real-shift identity) had left `b>2` with
arbitrary real shifts as the remaining gap.

## What was found, and when

Per the lane instructions the public registry and closest-theorem bodies were investigated
EARLY, before any formalization investment. Retrieval window 2026-10-28T17:17Z onward:

1. The **trureturing public registry** (the-omega-institute, "Discovering truth") contains a
   dedicated problem page for exactly this Conjecture 2
   (`karp-2016-incomplete-beta-first-parameter-coefficient-signs`), triaged **PROVED for all
   positive real a,b,alpha,beta and every natural n, both sign branches, neither shift
   restricted to integers**. The same registry separately records Conjecture 1 (phi_k) as
   PROVED and explicitly marks Conjecture 2 as not addressed there — the two records are
   distinct and consistent.
2. The settling certificate is a complete Lean development at commit
   `337295b0bdf0aa6e2e9393a3ccdf1cb63d3c5ebb` (commit dated 2026-10-28T16:10:44Z, i.e. about
   one hour before this lane's retrieval): `D5/S3/Analytic/IncompleteBetaShape/Result.result`
   proving `Defs.claim`. The actual Lean bodies were read (not inferred from metadata):
   - `coeff a b j = Gamma(a+b+j)/(Gamma(b)*Gamma(a+j+1))` — exactly `h_b(a+j)`, **no k!
     weighting**;
   - `psi a b alpha beta n` — exactly the displayed convolution difference;
   - `claim := forall a b alpha beta > 0 (real), forall n : Nat, (b<1 -> psi<0) /\ (1<b ->
     psi>0)` — exactly Conjecture 2, both branches, all real shifts;
   - `Result.lean` contains **0 occurrences** of sorry/admit/axiom/native_decide; the same
     holds for the dependency modules `Mixture.lean` (802 lines), `Kernel.lean` (347 lines),
     `Comparison.lean` (297 lines) and `IncompleteBeta/Defs.lean`. The frozen state record
     `Golden/Frozen/state/.../Result.lean.json` lists all five theorems of the module.
   - The problem page records the axiom closure as `{propext, Classical.choice, Quot.sound}`.
3. The proof route was **independently re-derived by hand in this lane** and agrees with the
   Lean development step for step (see discovery.md):
   - affine mixture identity: the uniform mixture of `Beta(p+k+1, q+n-k+1)` densities over
     `k=0..n` is the law of `s*V+(1-s)*U` with `s~Beta(p+q,n+2)`, `V~Beta(p,q)`, `U` uniform
     (re-derived exactly via the change of variables `(v,s) -> (x,z)=(sv,s(1-v))`, Jacobian
     `s`, expanding `(1-x-z)^n=((y-x)+(1-y-z))^n`);
   - kernel `H(c,n,b)(v)` = beta-average of `F_s(v)=int_0^1 [y(1-y)]^(b-1) |_{y=sv+(1-s)u}`;
     `F_s` is symmetric in `v` and strictly monotone toward 1/2 because
     `r(1-r)-l(1-l)=s(1-s)(1-2v)` for `l=sv, r=sv+1-s`;
   - convolution identity `S_n(p,q;b) = K(c,n,b) * betaMean(H; (p+q)/2,(p-q)/2)` with
     `K=(n+1)Gamma(c+n+2b)/(Gamma(b)^2 Gamma(c+n+2))` (matches the Lean `mixtureFactor`);
     hand-checked at `b=2, n=0`;
   - beta-mean strict comparison in the shape imbalance at fixed sum, with imbalances
     `|alpha-beta|/2 < (alpha+beta)/2`, gives both signs.
4. An independent numerical cross-check (`verify_route_chain.py`, saved output
   `verify_route_chain.json`, 30 dps, <512MiB, 70-node tanh-sinh rule per integral)
   confirms the identity chain on 8 parameter sets spanning b<1, 1<b<=2 and b>2 (max
   b=7.3), all real shifts and n<=5: `psi` by direct Gamma products equals `psi` via the
   H-kernel/beta-mean route to relative difference <= 4.5e-8 (quadrature-limited; most
   cases <= 1e-12), and both sign branches hold on every sampled case. Beta-shape
   parameters below 0.1 are excluded because the corresponding beta means concentrate
   below any reachable quadrature depth; the public Lean proof compares the means
   analytically and has no such limitation. This is consistency evidence for the public
   route, not a proof.

## Consequences for the campaign

- MathDB 331384 / Karp Conjecture 2 is publicly resolved. Under the batch rules a public
  proof/refutation cannot be credited, and formalizing it now would be a mere formalization.
  **Credit 0. No Lean bridge, manuscript, review or packet is started.**
- Root's uncounted partials (`1<b<=2` concavity argument; exact `b=3` identity) are strict
  sub-cases of the now-public full resolution; they remain uncredited and are now moot.
- The r17 `h=t^2, a=.01, alpha=beta=.1, k=1` counterexample (`psi=-3829/250000`) remains a
  valid refutation of the generic log-concavity route only; the public route does not run
  through generic log-concavity but through the exact shifted-beta mixture structure of the
  Gamma-ratio coefficients, consistent with that counterexample.
- MathDB 331384 itself was not edited or posted to (its live record still shows open status
  as of the root r6 snapshot; no external action taken by this lane).

## Limits

- This lane read the registry pages, the Lean sources and the frozen state at the pinned
  commit, but did **not** re-elaborate the Lean development with its own toolchain; the
  compile status is taken from the repository's frozen-state records and the registry's
  stated axiom closure. The hand re-derivation and the numerical cross-check above are this
  lane's independent verification of the mathematical content.
- No exhaustive citation audit was performed; irrelevant now, since a public complete
  certificate was located directly.
- One source family (Karp 1509.05120 Conjecture 2 and its public resolution) only.
