# W009 geometric-escape tests — independent review

2026-10-08. Independent T3 validator (Claude Opus 5.5). No recursive delegation,
candidate runs, prime or depth sweeps, shared-file, source, Lean or state edits,
packages, commits or publication. Verified factoring complexity improvement:
**NONE**.

Scope: the parent note [W009-geometric-escape-tests.md](W009-geometric-escape-tests.md)
§§1–4, plus the parts of [W009-odd-paired-fold.md](W009-odd-paired-fold.md) that
§1 depends on. Not reviewed: the live D four-fiber/Riemann–Hurwitz audit. Frozen
inputs: [inputs manifest](W009-escape-review-inputs.json). Certificates:
[W009-escape-review-check.py](W009-escape-review-check.py) →
[W009-escape-review-check.json](W009-escape-review-check.json), **419/419 passed**.
Delivery: [W009-escape-review-delivery-manifest.json](W009-escape-review-delivery-manifest.json).

## Verdict

Every displayed identity in the escape note is correct: (1)–(6), the isogeny
y-coordinate and target, the two-step composition with its signs and scaling, the
4^k law, and the curve-plus-twist count. The count holds for **all** m ≥ 1 and for
any good curve Y²=X³+AX²+BX, not only the full-2-torsion family. All the
non-novelty and negative conclusions survive. I found four material corrections
and three additions:

1. **No square root is needed for the coherent doubling chain** (correction to §2).
   A fold z−(y+w)+yw/z needs only the sum and product of its anchors. The dual
   edge has r'+s'=−2(r+s) and r's'=(r−s)². So (3) and (4) hold for **every** good
   pair (r,s), with checks on 2, r, s, r−s only. The family r=u², s=v² is needed
   only to make E' have full rational 2-torsion, which matters only for a
   **non-dual** next kernel (§4). Later stages are 4^j-scalings and need no
   further gcd checks.
2. **The explicit family is a known ECM torsion family** (addition to §2).
   R=(u²−v², 2u(u²−v²)) is a rational point of order 4 on E', with 2R=(0,0).
   Then E'(F_p) ⊇ Z/2×Z/4, so 8 | #E(F_p) at every good prime. This slightly
   raises the 2-power supply. Such torsion-boosted curves are standard ECM
   practice, not a new channel.
3. **The coherent elliptic version of the odd variant is a fixed CM curve**
   (addition). The odd fold z+c/z (c=−a²) is the kernel-(0,0) 2-isogeny of
   Y²=X³+cX. The free schedule c→−4c is x-only doubling on Y²=X³−a²X, which is
   the quadratic twist by a of Y²=X³−X. So the curve-plus-twist pair, and with it
   the whole supply law, **does not depend on the sampled anchor**. For p≡3 mod 4
   both orders are p+1. Then stage 2k has pole probability (gcd(p+1,2^{k+1})−1)/p.
   The torus schedule c→4c gives (gcd(p+1,2^j)−1)/p after j folds. Both saturate
   at the same 2-part of p+1, and the torus gets there in fewer folds.
4. **Denominator-only success is not stopped success** (correction to the scope
   of §3). The note itself warns against conflating them. The exact stopped law is
   given below. In a fixed instance (N=143, depth 6) per-stage gcds succeed on
   134/143 inputs, but the final denominator alone succeeds on only 88/143.
5. **Coalescing reduces to the odd variant only when S is carried** (scope of §1).
   On a generic P the coalesced fold G_y has a different law (below). In addition,
   gcd(U²,N)=gcd(U,N) needs squarefree N. If p²|N, squaring can turn a proper gcd
   p into N.
6. **The odd-stage pole law** is missing from §3 (addition, below).
7. The Kenku lead is correct as stated, but only for **cyclic isogenies over Q**
   (§4 scope below). It is not needed: the order law already settles the
   computation.

Strongest scoped result: on the coherent dual-cycle schedule at a good prime, the
pole set of the original fold chain is exactly an x-image of rational 2-power
kernels on E and its twist. So the elliptic-coherent fold is Lenstra ECM stage 1
on a single curve with multiplier 2^k only. It is dominated by ordinary ECM, whose
multiplier already contains 2^e. Depth cannot remove odd-order components.

## §1 Coalescing — verified, with scope

- G_{a²}(S²)=(S−a²/S)² holds. In projective coordinates it holds exactly, not just
  up to a scalar: G applied to [U²:V²] gives [(U²−a²V²)²:(UV)²], which is the
  square of the odd update [U²−a²V²:UV] (S1). The odd fold equals F_{a,−a}
  because S stays odd. Degree doubles per stage on both S and P. Costs are O(k²)
  to acquire and O(k) per probe.
- **Generic P (not a carried square).** G_y(z)=(z−y)²/z has involution z↦y²/z
  with c=y², which is always a square, and a ramified zero at y. Exactly, with
  legal probability s:
  Δm=ν(y), Δv=Γ(y²)−ν(y)², and raw moments E[1Δm]=v, E[1Δv]=Σν(y)Γ(y²)−u3
  (F5, symbolic weights over F_7). This agrees with the odd law after
  ν_P(a²)=2ν_S(a). These are different protocols, as the note says.
- **Odd-variant laws, all verified** (symbolic odd weights over F_7 and F_13, F4):
  - legal probability s;
  - Δm=2ν(a), Δv=Γ(−a²)−4ν(a)²;
  - E[1Δm]=2v, E[1Δv]=Σν(a)Γ(−a²)−4u3.
  - First-step residual mass is exactly (2p−6)/p² for p≡3 mod 4 and (2p−8)/p² for
    p≡1 mod 4, for every legal a (F3). With p≡3 mod 4 the involution has no fixed
    points.
  - Composite: by CRT independence of r mod p and r mod q, the raw moments at p
    are multiplied by s_q for a fixed map.
- **Frame alignment.** Hitting F(z)=±2a needs z∈a·{±1±√2}. The note's "1±√2"
  covers only the +2a branch. Locally these values can carry ν-mass when 2 is a
  QR. They are not impossible, just unpaid and uncontrolled. The verdict stands.
- **Fourier identity** verified exactly in Q(ζ_{p−1}) for p=7 (odd and non-odd
  weights) and p=13 (F6). Three refinements to the Parseval bound:
  - δ only has to bound |M(ψ)| over nontrivial **squares** ψ=η̄². For p≡3 mod 4,
    χ is not a square.
  - The χ term is s·χ(−1)·M(χ)²/(p−1), real but signed. The |·| bound is valid.
  - The identity is for C=ν∗ν, which includes the diagonal. The drift uses
    Γ(c)=C(c)−Σ_{z²=c}ν(z)². So Σν(y)Γ(−y²) equals the C-sum exactly when
    p≡3 mod 4, and the C-sum minus 2Σν(y)ν(iy)² when p≡1 mod 4. The bound is
    therefore an upper bound for the Γ-drift.

## §2 Elliptic coherence — identities verified, connection is standard

- E: Y²=X(X−r)(X−s), A=−(r+s), B=rs. X'=X+A+B/X=(X−r)(X−s)/X.
  With Y'=Y(1−B/X²), the target Y'²=X'³−2AX'²+(A²−4B)X' holds identically (S2).
  This Y' is Silverman's y(B−X²)/X² composed with [−1]: same x-map, same kernel,
  also an isogeny. E' is nonsingular iff B(A²−4B)=rs(r−s)²≠0.
- Doubling: x(2Q)=(X²−B)²/(4Y²), verified from the tangent law (S3).
- Two folds as exact projective polynomials:
  [(U²−rsV²)² : UV(U−rV)(U−sV)] (S4). This equals 4x([2]Q) on E or its twist.
- The u,v target anchors −(u∓v)² are verified, and so are r's'=(u²−v²)² and
  r'−s'=4uv. With N odd, the checks u, v, u±v make every chart a unit.
- After two folds the coefficients are A''=4A, B''=16B. The isomorphism is
  (X,Y)↦(4X,8Y), and F_{4r,4s}(4z)=4F_{r,s}(z).
- Explicit schedule for (4): odd stages use anchors 4^j(r,s); even stages use
  4^j(r',s'), or just the sum and product. P_{2k}=4^k·x([2^k]Q) was checked
  pointwise in F_{p²} for every x in three fixed chains, including two with rs a
  nonsquare (F2).
- The coherence caveat is correct. Any single sampled fold is a 2-isogeny x-map of
  E_{y,w}. But for successive sampled pairs the intermediate curves do not match,
  so point orders are not transported.
- **Duplicates W001 Card 3.** That card already has the edge (−2A, A²−4C), the
  dual return to (4A,16C), and [2] up to isomorphism. The genuinely new item is
  the observation that the W009 fold *is* this x-map. That is textbook
  (Silverman III.4.5; Vélu's 2-isogeny on the frozen MIT slide, in short
  Weierstrass form).

## §3 Curve-plus-twist count — proved for all m ≥ 1

Fix a good odd prime p (p∤2B(A²−4B)) and a nonsquare d. A point x∈P¹(F_p) lifts
to E(F_p), to E^d(F_p), or to both. It lifts to both exactly at the rational
branch points: ∞ and the rational roots of the cubic, where the lifts are
2-torsion of equal order. The pole of the x([m])-map at x is intrinsic: the
circuit has no basepoints, so V vanishes exactly there.

**Lemma.** Let H≤E(F_p) and H^d≤E^d(F_p) be subgroups whose 2-torsion parts have
the same x-coordinates. Then #x(H∪H^d) = (|H|+|H^d|)/2.
Proof: negation pairs the points outside H[2]. So #x(H)=(|H|+|H[2]|)/2, and the
overlap is exactly x(H[2]).

- Taking H=E(F_p)[m] gives (5) with t_m=|E(F_p)[gcd(m,2)]|, which is equal on the
  twist. Taking away x=∞ gives (6).
- Certified independently of the twist argument in F1. There, [m]Q was computed in
  F_{p²} for every x, for all m in [1, 2p+3], on three fixed curves. One of them
  has a single rational 2-torsion point. 83 checks.
- Invariant-factor form: a_{2^k}=gcd(a,2^k)·gcd(b,2^k). This saturates at the
  2-primary size, whereas the geometric pole divisor of x∘[2^k] has degree 4^k.
  These are different objects.
- **Odd-stage law (new).** Stage 2k+1 has a pole iff [2^k]Q∈{O,(0,0)}. Its affine
  count is (|S_E|+|S_{E^d}|)/2−1, where
  |S_E| = a_{2^k}·(1+[(0,0)∈2^k E(F_p)]). Verified for all stages 1–8 in F2.
- **Stopped versus final-only.** ∞ is absorbing. Let τ_p be the first stage with
  V≡0 mod p. With fresh uniform x mod N, τ_p and τ_q are independent.
  - Per-stage gcds with first-failure stopping succeed iff τ_p≠τ_q and
    min(τ_p,τ_q)≤D, i.e. with probability 1−Σ_j Δh_p(j)Δh_q(j) − (1−h_p(D))(1−h_q(D)).
  - The note's h_p(1−h_q)+h_q(1−h_p) is the probability of a single final
    denominator test only.
  - F8 checks both laws exactly on N=143 (134 vs 88 of 143 inputs). This is one
    toy certificate, not evidence of a speedup.
  - Numerator channels (x([2^k]Q)=0 ⇔ [2^k]Q=(0,0)) and other gcds are separate
    coset unions, as the note says.
- **Comparison with ECM.** This is Lenstra (2.4) with k=2^K on one curve. The
  random x selects E or its twist, as in standard x-only (Montgomery-style)
  arithmetic. The twist's order is 2p+2−#E, so it is not a fresh trial. Lenstra's
  (2.6) needs an annihilating multiplier that covers the point order, so a pure
  2^K multiplier only ever catches 2-power orders.

## §4 Non-dual kernels and the Kenku scope

- Translating by r gives roots 0, −r, s−r and B_r=r(r−s) (S6). Kernel (r,0) is
  itself free. What costs a root is a **non-backtracking second step**: the target
  roots A_r±2√B_r need √B_r, which is u√(u²−v²) in the family.
- Kernels of degree 2^k leave every odd-primary part of a point's order unchanged:
  ord(φQ)=ord(Q)/|⟨Q⟩∩ker φ|, as in W001 Card 3.
- Kenku, as read from the frozen Banwait slide: IsogCyclicDeg(Q) =
  {1,…,19}∪{21,25,27,37,43,67,163}. So a cyclic Q-isogeny of degree 2^k exists
  only for k≤4. This is a secondary source; Kenku's originals were not read.
- Scope of Kenku: elliptic curves and isogenies defined over Q only.
  - Over F_p, any rational point of order 2^k gives an F_p-rational cyclic subgroup
    and, by Vélu, an F_p-rational cyclic 2^k-isogeny. This is standard and not
    certified here.
  - It says nothing about coefficients mod N that depend on N, and the parent
    correctly declined to transfer it.
  - It is irrelevant to the conclusion, which follows from the order law alone.

## Subgroup images versus perfect powers

The only power structure claimed is the literal P=S² of §1. Rational images lying
in 2^k E(F_p) or in a torus subgroup do not make the circuit a geometric 2^k-th
power, and nothing in the note or this review infers that.

## Next decisive question (for the parent)

No identity here supplies a useful correlation outside the 2-power index. Each
cheap coherent schedule tested has a fixed group whose order does not depend on
the samples:
- the dual cycle: E and E^d;
- the odd variant with c→−4c: the CM pair attached to y²=x³−x;
- the torus c→4c: p±1.

Any escape must name a paid transfer that changes the group order. It must then be
compared with fresh-curve ECM at equal work, not with deeper doubling.
