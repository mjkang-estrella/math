# I305 — positive curvature and quadratic boundary folding

2026-10-13. **Parent proof proposal; no independent proof or contribution verdict.** Thirteen findings remain accepted. This is a possible quantitative continuation of I214, whose proof passed I218 but whose contribution was classified TECHNICAL by I219. It is not a re-nomination of I214's global univalence alone.

## Exact proposed statement

Let Ω be a nonempty bounded smooth convex planar domain whose boundary curvature κ is strictly positive everywhere. Let μ be its first positive Neumann eigenvalue and suppose its real eigenspace V has dimension two. For every real basis u,v of V, write F=(u,v). Stipulate the pinned OpenAI gradient theorem at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Use the downstream I214 theorem only with its independently passed I218 proof: F is a diffeomorphism of interiors and homeomorphism of closures onto a bounded smooth strictly star-shaped domain U containing zero; its boundary restriction is a smooth diffeomorphism, and F kills the inward normal on the boundary.

The proposed new conclusions are:

1. At every p in ∂Ω the second normal derivative of F has a strictly inward component relative to ∂U. In particular it is not tangent to ∂U.
2. There are smooth source and target boundary coordinates at every such point in which F is exactly (s,t) ↦ (s,t²), with t≥0 on the source and the second target coordinate nonnegative inside U.
3. There is a constant C depending on Ω and the chosen basis such that

       |x-y| ≤ C |F(x)-F(y)|^(1/2)  (x,y in closure Ω).

   The exponent 1/2 cannot be increased, even locally at a single boundary point. No effective or geometry-uniform value of C is claimed.
4. For counterclockwise unit-speed p(s) on ∂Ω, put γ(s)=F(p(s)). After orienting the basis so that F preserves orientation,

       μ det(γ,γ') - det(γ',γ'') > 0.             (K305)

   Reversing the basis reverses the displayed determinant inequality. An orientation-free statement is conclusion 1.

Strictly positive curvature is an explicit hypothesis. Smooth strict convexity with possible zero curvature is not silently included. No claim concerns unequal eigenvalues, higher modes, holes, or arbitrary smooth boundary maps.

## Proposed proof

Use inward normal coordinates x(s,t)=p(s)+t n(s), where p is counterclockwise unit-speed, n the inward unit normal, p''=κn and n'=-κp'. Set H(s,t)=F(x(s,t)); then H_t(s,0)=0 and H(s,0)=γ(s). The metric is (1-κt)² ds²+dt². Applying the scalar Laplacian componentwise gives

    H_tt - κ/(1-κt) H_t
      + (1-κt)^(-2) H_ss
      + t κ'/(1-κt)^3 H_s = -μ H.

Let A=H_tt(s,0). At the boundary, therefore,

    A=-μγ-γ'',
    H_ttt(s,0)=κA-2κγ''-κ'γ'.                  (1)

Here H_st=H_sst=0 on t=0 by tangential differentiation of H_t=0. In particular no derivative of the eigenvalue or of a varying coefficient is omitted.

Fix s=s0 and choose a local smooth defining function ρ for U with ρ<0 inside, ρ=0 on its boundary and nonzero outward gradient there. Write ℓ=dρ at γ(s0). Then ℓ(γ')=0 and ℓ(γ)>0 by strict star-shapedness. Since F maps the interior to U,

    h(t)=ρ(H(s0,t))<0 for t>0 small,
    h(0)=h'(0)=0,
    h''(0)=ℓ(A)≤0.                             (2)

If ℓ(A)=0, equation (1), together with A=-μγ-γ'', gives

    h'''(0)=ℓ(H_ttt)=2κμℓ(γ)>0.

All terms involving H_t in the third derivative of ρ(H) vanish. Taylor's formula would then make h(t)>0 for small positive t, contradicting (2). Hence ℓ(A)<0. This is the claimed nondegenerate quadratic inward motion. With F orientation preserving, U is on the left of γ', and det(γ',A)>0 is equivalent to that inward motion. Expanding A proves (K305).

For completeness, the exact normal form needs no appeal to a classification theorem. Take a local smooth tangential coordinate σ on U whose restriction to ∂U has nonzero derivative along γ. Put v(s,t)=-ρ(H(s,t)). It is smooth, v(s,0)=v_t(s,0)=0 and v_tt(s,0)>0. The integral Taylor formula factors

    v(s,t)=t² b(s,t),
    b(s,t)=integral_0^1 (1-r) v_tt(s,rt) dr >0

in a sufficiently small neighborhood. The source change (s,t) ↦ (σ(H(s,t)), t sqrt(b(s,t))) is a smooth local boundary diffeomorphism: at t=0 its Jacobian is the product of a nonzero tangential derivative and sqrt(b)>0. The target coordinates are (σ,-ρ). Thus F becomes precisely (α,β) ↦ (α,β²) on β≥0.

This normal form gives a local 1/2-Hölder inverse, since |sqrt(v)-sqrt(w)|≤sqrt(|v-w|) for v,w≥0. Smooth chart changes are Lipschitz on smaller compact neighborhoods. On compact subsets of the interior, the inverse is smooth and locally Lipschitz, hence locally 1/2-Hölder after bounding the distance. Choose finitely many such image neighborhoods covering closure U. Their Lebesgue number controls every sufficiently close pair of image points by one local estimate; distant pairs are controlled by the diameter of Ω. This proves conclusion 3 globally. The statement uses Euclidean distance and does not require U to be convex.

Finally F(p+t n)-F(p)=t² A/2+O(t³), with A having a nonzero normal component. Hence the image distance is comparable to t². An inverse Hölder bound of exponent α>1/2 would imply t≤C t^(2α), impossible as t decreases to zero. This also recovers I214's non-Lipschitz limitation and makes its rate precise.

## Prior-art check and remaining contribution question

The new-looking step is a third-order boundary contradiction using positive curvature and the star-shaped eigenmap image. A primary source located during this derivation warns against overclaiming novelty: Bañuelos and Pang, *Level sets of Neumann eigenfunctions*, https://www.math.purdue.edu/~banuelos/Papers/neumann.pdf, already uses positive curvature to control a third normal derivative when the second one vanishes. The complete 16-page web text (lines 0–766) was read, with the operative comparison in Proposition 2.2 and Section 4, especially equations (4.1)–(4.8). Their conclusion concerns finiteness of connected level-set components of a single first-positive eigenfunction; it is not stated as a two-mode fold theorem or inverse Hölder estimate. Their cubic derivative mechanism is nevertheless an important prior ingredient. Neither its age nor the different conclusion proves that the present deduction is substantial.

The source PDF was read through its web text; its plots and page images were not inspected, and no PDF raw hash is claimed. No external full text is newly retained. Broad search hits about high-frequency eigenfunctions, Neumann domains and harmonic maps are not used as premises. The proposed proof above derives its local differential identities directly.

I219's full negative contribution review and I218's full positive proof review were re-read. I214's downstream global theorem is a valid available lemma but does not itself count as substantial. A fresh review would have to judge the entire added boundary statement against the known cubic derivative method, not count the normal form or Hölder corollary separately. Until then this is an unaccepted candidate, with a material risk of another TECHNICAL verdict.
