# W026 review: affine multipliers and the exceptional residue

2026-10-08 local / 2026-10-09 UTC. **Accept as an admissibility and coverage primitive, with the explicit conventions below. The generic affine gain is rejected, as already stated in the brief. No structured candidate with a proved net advantage or complete factoring improvement is established. Verified improvement: NONE.**

This review concerns frozen W026 SHA-256 `19de795d800e2c864851d3cd0b0c32640aec138b8361bae8ebaca9759929d65d`. The [complete assignment](W026-affine-exception-review-evidence/brief.txt), [input manifest](W026-affine-exception-review-evidence/input-manifest.json), and [read scope](W026-affine-exception-review-evidence/read-scope.md) fix the boundary. W022 root charts, W024's sign/prime schedule, W025's fixed-dimensional acquisition theorem, and W020's extractor are imported at their accepted interfaces. Their certificates were not re-audited. No experiment or new prior-art claim is needed for this symbolic verdict.

## 1. Exact feasibility and normalization

Use a nonempty integer coordinate interval I=[l,h], Z=max(1,|l|,|h|), Q=ell^L with L>=1, and an exactly encoded T>0. The original root representative R has degree at most 4. Coefficients can first be reduced modulo Q: changing their representatives only shifts the integer k_i variables. Write d_-1=d_5=0 and f_i(a,b)=a*d_i+b*d_(i-1).

For each active i, partition [0,Q) into K_i half-open intervals of width Q/K_i. More than product K_i points (a,b) in [0,C0] x [0,C1] force two residue vectors into the same box. Subtracting their *integer* coordinates gives a nonzero pair within the symmetric caps and

```
e_i = a*d_i+b*d_(i-1)-Q*k_i,
|e_i| < Q/K_i,
|e_i| <= ceil(Q/K_i)-1 = floor((Q-1)/K_i).
```

The strict pigeonhole inequality and half-open boxes are sufficient exactly as written. No enumeration of the rectangle is required by the algorithm. The four systems with a>=1, a<=-1, b>=1, or b<=-1 cover precisely the nonzero integer pairs, including either zero-coefficient case. Each system has at most eight integer variables (a,b and six k_i), independent of input size. Importing the accepted fixed-dimensional integer-feasibility theorem therefore gives polynomial bit-time acquisition, including an actual feasible point. With 0<=d_i<Q and caps below Q, any feasible k_i has O(log Q) bits. If the pigeonhole condition fails, feasibility may still hold; if all four systems fail, a separately priced c=1 fallback is available. That fallback need not meet the failed caps or the attempted T bound.

Let r=ell^min(v_ell(a),v_ell(b)), interpreting v_ell(0)=infinity. Since one coefficient is nonzero and has absolute value below Q, r<Q. Thus Q'=Q/r>=ell and c'=a/r+(b/r)x is primitive modulo ell. Every active e_i is divisible by r and

```
e_i/r = (a/r)*d_i+(b/r)*d_(i-1)-Q'*k_i.
```

Keep these divided errors as active coefficients and center inactive coefficients modulo Q'. For an active term, |e_i/r| Z^i < Q' Z^i/K_i <= Q'T; an inactive term is at most Q'Z^i/2 <= Q'T/2. Consequently P has degree at most 5, P congruent to c'R modulo Q', and |P(x)|<=6Q'T.

At a covered point, S congruent to sigma R modulo Q implies the exact representation

```
c'(x) S = sigma P(x)+Q' tau,
|tau| <= K := ceil((C0+C1 Z)W/Q+6T).
```

Here |c'|/Q' = |c|/Q pointwise; the larger modulus is not retained after dividing the errors. Negative coefficients and signs cause no change. If a=0, b nonzero, normalization can give a multiple of x, with exceptional residue zero. If b=0, a nonzero, it gives a nonzero constant modulo ell and no exception. The pair (0,0) is excluded before taking valuations. Dividing by r does not require r to divide the inactive coefficients chosen *before* normalization: those coefficients are chosen anew modulo Q'.

Because u(x),v(x) are affine on this one-coordinate chart, c'(x)(u+Nv) has degree at most 2. Thus

```
E'(x,tau)=c'(x)(u+Nv)-sigma P(x)-Q' tau
```

has degree at most 5 in the coordinate, is linear in tau, and equals c'(x)(p-1)(vq-u) at the covered leaf.

## 2. Exact endpoints and the exceptional path

The imported sign contract is u(x)+Nv(x)-sigma R(x) congruent to epsilon modulo ell for *all* coordinates, with epsilon nonzero. Therefore every represented E' is congruent to epsilon*c'(x), independently of tau.

If b/r is zero modulo ell, a/r is nonzero and the entire interval is safe. Otherwise the unique exceptional residue is j0=-(a/r)*(b/r)^(-1) modulo ell. For each canonical j in {0,...,ell-1}, substitute x=j+ell*y on the exact interval

```
ceil((l-j)/ell) <= y <= floor((h-j)/ell).
```

Discard empty intervals. Mathematical floor/ceiling handles negative endpoints; replacing division by truncation toward zero does not. The nonempty residue intervals are disjoint and cover I exactly. All j!=j0 are retained, with constant nonzero residue epsilon*c'(j), the substituted polynomial, and the same safe carry interval [-K,K]. Although substituted coefficients may be larger, the polynomial's value bound on that restricted interval is inherited from its parent.

For j0 retain R(j0+ell*y) modulo the **original Q**, along with the transformed u,v and the same root sign and bound W. Its original unscaled exponent still has residue epsilon. Acquire a fresh multiplier relative to this root congruence, with fresh endpoint-derived Z and paid carry bound. Previous scaled P or Q' is not the root input to the exceptional child. A c=1 fallback here uses the centered original quartic and, for example,

```
|tau| <= ceil(W/Q + (1/2)*sum_(i=0)^4 Z^i).
```

At a singleton x=x*, evaluate and center rho=R(x*) modulo Q, use c=1, and enumerate the exact finite interval

```
ceil((-W-sigma*rho)/Q) <= tau <= floor((W-sigma*rho)/Q).
```

This covers every possible true S with |S|<=W and S congruent to sigma*rho modulo Q. It needs no knowledge of S or its actual carry. If the interval is empty, there is no covered S there. The singleton's carry count can still be large and is charged.

If a node contains n>1 integers, its exceptional child has at most ceil(n/ell) integers and strictly fewer than n. For n0=|I|>=1, D=ceil(log_ell n0) bounds the number of nonsingleton exceptional steps. There are at most (ell-1)D+1 nonempty retained coordinate intervals and at most 4D integer-feasibility calls, with earlier constant/empty-branch termination allowed. n0=1 uses the singleton rule directly; n0=0 contributes product 1. Thus the claimed O(ell log(length)+1) record and O(log(length)+1) acquisition bounds are valid, with the constants and singleton convention made explicit.

Every covered coordinate either exits into a safe interval or reaches the singleton fallback. Its true carry is covered by the corresponding bound. No assumption about the hidden witness avoiding j0 is used.

**Why the branch is necessary.** Take p=5, q=7, ell=3, M=9, u=1, v=2. Then up-vq=-9, S=19, and E=52 is nonzero modulo 3. The legal u-chart u=1+3x includes x=0 (for example U=4, V=3); its root can have R(0)=19 modulo 81. The admissible polynomial c=x vanishes at this covered point. Keeping its zero-residue class would admit E'=0, while deleting that coordinate loses this witness. The original-root c=1 fallback restores E=52. This is a hand-derived counterexample to omitting the exceptional branch, not a numerical run or a counterexample to W026.

## 3. Frozen products, bit widths, and W020

Finish constructing the retained affine family before product localization. The exceptional construction partitions *coordinates and covered witnesses*; changing multipliers does not factor the old exponent product. Define the new product over its final labeled records. During localization, retain each record's multiplier, polynomial, modulus and carry interval, and split the list or an ordinary interval disjointly. Empty products are 1. These restrictions give exact product identities and public singleton decoding.

Reacquiring a multiplier during localization requires a separate product-preservation argument, not just a setup charge. For example, modulo 15 with alpha=2, replacing exponent 4 by exponent 1 changes a full nonunit leaf 1-2^4 into the unit leaf 1-2. Both exponents are nonzero; nonzero residues alone do not preserve a previously detected collision. W026's stated option of keeping the polynomial on restrictions supplies the needed convention.

Let C*=C0+C1 Z. All represented exponents satisfy the explicit bound

```
|E'| <= (C*/r)(U+NV+W) + 12Q'T + Q'.
```

This follows by inserting |P|<=6Q'T and Q'K<=C*W/r+6Q'T+Q'. With exactly encoded public data of B bits, fixed degree gives polynomial binary width and polynomial feasibility/setup work. If Q,Z,U,V,W,T are N^O(1), all these widths are O(log N). Repeated affine substitution preserves degree; reducing each new root coefficient modulo the original Q prevents unnecessary growth. The accumulated coordinate map has O(log(|I|+1)+log ell) scale bits, and its initial endpoints remain charged. A constant number of field operations for j0 is polynomial bit work, not free arithmetic.

Uniformly, acquisition per supplied chart is bounded by

```
O((1+ell*D)*poly(B)),
```

including the constant number of fixed-dimensional solves per level, substitutions, residue endpoints and retained records. The imported public schedule has ell polynomial in bitlen(N), so this is polynomial logarithmic overhead in the accepted parameter regimes. Sum it over every chart, stratum, factor range and scheduled prime.

Every final leaf has a nonzero integer exponent because its residue modulo ell is nonzero. For a scheduled good base, a covered leaf survives with exponent c'(x)(p-1)(vq-u), hence 1-alpha^E' is nonunit for every unit alpha. Use the original alpha sampled exactly uniformly from 1,...,N-1; signed powers use its checked inverse. The multiplier computation and exceptional path are public and alpha-independent. The full public schedule therefore preserves W020's pointwise coverage and nonzero-exponent contracts. The original even/perfect-power preprocessing, complete trial schedule, leaf localization and full two-adic recovery remain necessary. Conditional on a finite correct evaluator/localizer of complete-trial cost C_eval and acquisition P_acq, the imported expected bound is P_acq+2C_eval, with preprocessing added. This is not an improved bound on C_eval.

In particular, the products still contain sum_J |J|(2K_J+1) occurrences for symmetric-carry records, with exact singleton lengths substituted where used. Small record count or exponent bit width does not pay this bill. Explicit anchors can still share babies by their ell-power Q' as in the accepted W025 consumer, but there is no new joint-anchor computation or free sharing of the nonlinear coefficient arrays. The M-record one-fifth envelope is not removed.

## 4. The rejected generic frontier checks exactly

For exponent bookkeeping, put A=Z^s, C0 asymptotic to C, C1 asymptotic to C/Z, C asymptotic to T/A and T=Z^t. The rectangle volume is asymptotic to C^2/Z in the stated regimes. Integer ceilings and the strict existence inequality require fixed slack; caps below Q must also be checked.

For 0<=s<=1, degrees 3,4,5 are active, with degree 3 inactive exactly at the boundary t=3. The box count has exponent 12-3t. Balancing gives

```
2(t-s)-1 = 12-3t,  hence t=(13+2s)/5.
```

For 1<=s<=2, degrees 4,5 are active and

```
2(t-s)-1 = 9-2t,   hence t=(10+2s)/4.
```

Both active sets are self-consistent and agree at s=1. The exponents of C/Z are (8-3s)/5 and (3-s)/2, respectively, so the linear-coefficient cap does not collapse below 1. Relative to the constant-multiplier envelope (7+s)/3, the exponent losses are respectively

```
(4+s)/15 > 0,       (1+s)/6 > 0.
```

Thus this sufficient generic construction loses even before exceptional-branch/product costs and before the stronger precision-truncation comparator. This is neither an optimality theorem for the affine integer program nor a lower bound for structured coefficients or factoring.

## 5. Exact cancellation and the corrected W025 wording

The cancellation claim uses **both** inherited divisibilities d3=H^3*D3 and d4=H^4*D4 modulo Q=H^5, with D3 a unit modulo ell. Then c=1+H*b1*x gives

```
coefficient_4(cR) = H^4(D4+b1*D3),
coefficient_5(cR) = H^5*b1*D4.
```

Choose b1=-D4*D3^(-1) modulo H. This cancels both coefficients modulo H^5. Centering b1 gives |b1|<=H/2, hence the true-value multiplier bound 1+(H^2/2)Z. Its carry-width contribution is O((1+H^2 Z)W/Q). Reducing precision to H^4 with c=1 already deletes the quartic, with contribution H*W/Q and degree at most 3. There is no net gain from cancellation alone. Also c is identically 1 modulo ell, so this example has no exceptional branch at all.

The fourth-degree divisibility is supplied by the W022 coefficient structure, but cannot be omitted from a standalone assertion. For example, H=3, Q=243, d3=27, d4=1 meets the cubic-unit premise alone; 1+81b1 can never be zero modulo 243. This hand calculation is outside the structured-root promise and explains the necessary hypothesis. Within that promise, an advantage requires actual public coefficient correlations and caps cheap enough to beat the paid truncation/hybrid baseline, across all retained branches and evaluator costs. None is established here.

The sentence in W025 §6, “E'=c'(p−1)(vq−u) is nonzero exactly when p≢1 (mod ℓ),” is false if “nonzero” refers to the integer. The equivalence concerns the residue and true-leaf filter retention (for a primitive constant multiplier). With p=7, q=11, ell=3, u=2, v=1, one has up-vq=3, S=25 and E=2+77-25=54, a nonzero integer discarded by the residue filter. W026 must use the residue statement, which is sufficient. The W025 report itself was not edited.

## Disposition and next decisive object

**Revised/accepted admissibility primitive; generic gain rejected.** The exact feasibility proof, normalization with zero coefficients, at-most-one exceptional residue, original-modulus recursion and good-base W020 composition survive. Explicit endpoints, priced fallbacks, frozen products during localization, and the inherited d4 divisibility complete their scope.

The next evidence that could change the cost verdict is one public structured affine acquisition with proved cheap caps, all exceptional-path carry bounds, and a concrete paid consumer/localizer that beats the best constant/truncation/hybrid option on the same covered family. Another root or residue certificate does not supply it. The parent can continue its separate single-coefficient route independently.

No experiment, sweep, solver/Lean change or build, STATE/task edit, installation, delegation or commit occurred. Only this report and its assigned evidence directory were written. [Integrity verification](W026-affine-exception-review-evidence/verification.json) and the [delivery inventory](W026-affine-exception-review-evidence/delivery-manifest.json) record the final file boundary. **Verified complete factoring improvement remains NONE.**

At handoff all frozen hashes matched. Live research/STATE.md and W025-consumer-and-cost-frontier.md had changed; their new contents were not substituted into this frozen review. The W026 brief and the other load-bearing inputs still matched.
