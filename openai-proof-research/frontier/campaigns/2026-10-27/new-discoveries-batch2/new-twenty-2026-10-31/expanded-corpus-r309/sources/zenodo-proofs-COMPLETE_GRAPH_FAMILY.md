# Arbitrarily large strict counterexamples on weighted complete graphs

## Theorem: a two-level integer family in every order n >= 4

For any integer `m >= 3`, take the complete graph on one distinguished hub `0` and `m` outer vertices. Give every hub–outer edge conductance `2m−1` and every outer–outer edge conductance `2m−5`. All conductances are positive integers.

Let `D_m=2m²−3m−1`. Then its resistance curvature is

`p_0 = −1/D_m < 0`,

`p_i = (2m−3)/D_m > 0` for every outer vertex.

Nevertheless every elementary resistance-capacity submodularity inequality is **strict**. Therefore Conjecture 7.6 has counterexamples on complete graphs of every order `n=m+1>=4`, with only two integer conductance values. For each fixed order, continuity also yields a nonempty open set of fully supported positive conductance assignments that are counterexamples.

The integer ratio tends to one with growing order:

`(2m−1)/(2m−5)=1+4/(2m−5) -> 1`.

Thus the relative conductance contrast can be arbitrarily close to one, although the number of vertices increases and the negative curvature magnitude tends to zero. This is not an assertion of robustness uniform in order.

## Exact classification of the whole symmetric two-level family

Normalize outer conductance to one and let hub–outer conductance be `t>0`. The resistance distances are

`R_0i=(t+1)/[t(t+m)]`,

`R_ij=2/(t+m)` for distinct outer vertices.

Indeed the Laplacian acts by `t+m` on outer differences and by `(m+1)t` on the group-constant difference, yielding these formulas. The hub curvature is

`p_0=[m−(m−2)t]/[2(t+m)]`.

For a nonempty subset with `h in {0,1}` hubs and `k` outer vertices, put

`β(h,k)=(1ᵀ R[S]⁻¹ 1)⁻¹`,

with `β=0` on a singleton. Block inversion gives

`β(0,k)=2(k−1)/[(t+m)k]` for `k>=1`;

`β(1,k)=k(t+1)²/[2t(t+m)(t+k)]` for `k>=0`.

The full-set value is `B=β(1,m)=m(t+1)²/[2t(t+m)²]`. Under the normalization used in the original conjecture, capacity equals

`τ(empty)=0`, `τ(S)=1/2+β(h,k)/(2B)`.

Equivalently, define `A=2t(t+m)/[m(t+1)²]`. Then

`τ(0,k)=1/2 + A(k−1)/k`;

`τ(1,k)=1/2 + k(t+m)/[2m(t+k)]`.

No matrix inversion remains in the final formulas.

## Complete elementary-gap proof

For an elementary inequality let the base subset have `h` hubs and `k` outer vertices.

1. **Two outer vertices added, no hub in the base (`h=0,k>=1`):**

   `gap = 2A/[k(k+1)(k+2)] > 0`.

2. **Two outer vertices added, hub in the base (`h=1,k>=0`):**

   `gap = t(t+m)/[m(t+k)(t+k+1)(t+k+2)] > 0`.

3. **Hub and an outer vertex added (`h=0,k>=1`):**

   `gap = t(t+m) F_k(t)/[2m(t+1)² k(k+1)(t+k)(t+k+1)]`,

   where `F_k(t)=4(t+k)(t+k+1)−(t+1)²k(k+1)`.

4. **Empty base, hub and an outer vertex added:**

   `gap = t(m−1)/[2m(t+1)] > 0`.

5. **Empty base, two outer vertices added:**

   `gap = [(m−2)t²+m]/[2m(t+1)²] > 0`.

The only possible obstruction is case 3. Because

`(t+k)(t+k+1)/[k(k+1)] = (1+t/k)(1+t/(k+1))`

decreases with positive integer `k`, its sign condition is hardest at `k=m−1`. Thus the capacity is submodular **if and only if**

`F_{m−1}(t)=4(t+m−1)(t+m)−m(m−1)(t+1)² >= 0`.

All elementary gaps are strictly positive precisely when this inequality is strict.

For `m>=3`, put

`A_m=m²−m−4`, `B_m=−2m²+10m−4`, `C_m=3m(m−1)`.

The exact upper endpoint is

`t_max(m)=[B_m+sqrt(B_m²+4 A_m C_m)]/(2 A_m)`.

The capacity is submodular exactly for `0<t<=t_max(m)`. It is a counterexample exactly for

`m/(m−2)<t<=t_max(m)`.

(The interval is nonempty, as the explicit integer construction below proves.)

## Elegant explicit parameter and curvature

Choose `t=(2m−1)/(2m−5)`. Direct cancellation gives

`F_{m−1}(t)=8(m−2)/(2m−5)² > 0`;

`p_0=−1/(2m²−3m−1)`;

`p_i=(2m−3)/(2m²−3m−1)`.

These are closed symbolic identities valid for all `m>=3`, not a numerical extrapolation. Scaling all conductances by `2m−5` gives the integer weights in the theorem and leaves curvature and normalized capacity unchanged.

The capacities specialize to

`τ(0,k)=1/2 + [(2m−1)D_m/(2m(2m−3)²)](k−1)/k`,

`τ(1,k)=1/2 + k D_m/[2m(2m−1+k(2m−5))]`.

At `m=3` this is the four-vertex graph with conductance 5 on the three hub edges and conductance 1 on the outer triangle, with curvature `(-1/8,3/8,3/8,3/8)`.

## Scope

This family strengthens the fixed-weight disproof in order, strictness, density, integer simplicity, and arbitrarily small relative weight contrast. The complete support graph itself admits other resistance-nonnegative weightings, so this construction does not establish the graph-level Conjecture 7.7 disproof. The separate five-vertex `K2 join independent3` graph supplies that result.

The hub curvature here approaches zero from below as `m` grows. It does not prove an unbounded negative-curvature phenomenon under submodularity.

## Sharp certificate margin for the integer family

The smallest of **all** elementary τ-gaps is exactly

`G_m=(2m−1)(m−2)/[m²(m−1)(2m−3)²(2m²−5m+4)] > 0`.

It is attained precisely when the base consists of `m−1` outer vertices and the two added vertices are the hub and the missing outer vertex. There are `m` such inequalities.

Here is a direct comparison proof. The mixed gap at base size `k` can be written

`A/[k(k+1)] * (1−Q_k)`,

where `Q_k=(t+1)² k(k+1)/[4(t+k)(t+k+1)]`. The first factor decreases with `k`; `Q_k` increases, and is less than one throughout the family. Thus the mixed-gap minimum is attained at `k=m−1`, where substitution gives `G_m`.

The two outer–outer gap classes also decrease with the base size, so their minima occur at `k=m−2`. Put

`u=2m−5`, `v=2m−1`, `w=2m−3`,

`D=2m²−3m−1`, `E=2m²−5m+4`, `H=2m²−7m+9`.

The minimum gap in each of the other four classes is

| Class | Minimum |
|---|---|
| two outer vertices, nonempty base without hub | `vD/[m²w²(m−2)(m−1)]` |
| two outer vertices, base containing hub | `vu/[mHE]` |
| hub and outer vertex, empty base | `v(m−1)/(4mw)` |
| two outer vertices, empty base | `[(m−2)v²+mu²]/(8mw²)` |

Dividing these by `G_m` yields, respectively,

`DE/(m−2)² > 1`;

`u m(m−1)w²/[H(m−2)] > 1` (use `H<mw`);

`m(m−1)²wE/[4(m−2)] > 1`;

`m(m−1)E[(m−2)v²+mu²]/[8v(m−2)] > 1`.

Each strict inequality follows immediately for `m>=3` from the displayed positive factors; in the last row retain only `(m−2)v²` in the square bracket. Hence no other class attains the minimum.
