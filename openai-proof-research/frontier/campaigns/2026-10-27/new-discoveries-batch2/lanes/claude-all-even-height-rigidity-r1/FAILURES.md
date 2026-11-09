# Failures and dead routes (all preserved; none hidden)

Each item states the route, the exact failure witness, and where its output is stored.

1. **Blind local search (lattice boxes).** This route is invalid as evidence.
   * Planar control (9×9 box, 200k iterations × 3 restarts): best 31–33 odd directions, even though planar
     all-even sets exist.
   * 3-D 4³ box: best 61–67.
   * Because the search fails even on the planar control, its 3-D failure says nothing about the conjecture.
     Outputs: `runs/ls_planar_control.out`, `runs/ls_3d.out`.
2. **Lattice-convex family (Observation E).** No example was found even in 2-D (best 2 odd directions).
   In 3-D the best was 6, in 4-D 11. Output: `runs/latconv_*.out`.
3. **Products Q×H.** Source all-even Q times nine different H gives 26–339 odd directions. Prop C closes only
   the case c_g(H) odd. Output: `runs/products.out`.
4. **Point-group orbits** (T_d, T_h, O, O_h, I, I_h, D_n, D_nd, D_nh, C_nv, S_2n for n = 3, 5, 7, 9; 13 base
   points; unions of two orbits at radii 1, ½, 2). The best is 3 odd directions, from the octahedron, which
   is centrally symmetric. Generic orbits have singly-determined chords. Output: `runs/orbits.out`.
   Float mode only.
5. **Spherical exhaustive F₂-quadratic search.** These configurations have no three collinear points, so
   *all* 2^N subsets were enumerated (N ≤ 22). Universes tested:
   * truncated tetrahedron, icosahedron, cube∪octahedron;
   * ring configurations 6/6/6, 8/6/6, 7/7/7, 9/6/6, 10/5/5, 5/5/5/5, 12/4/4, 13/4/4, 15/3/3, 13/5/4,
     15+6, 13+8.

   The only solutions are coplanar cyclotomic sets: exactly the source's Table 1 strings for n = 13, 16 and
   P15∖P3. There are no spanning solutions.

   Positive controls P13/P15/P16 recover 39/5/16 planar solutions. This is support evidence only: it covers
   finitely many universes, with float direction keys (6 digits).

   **Universe-definition bug:** `cubocta_12` merged two overlapping T_d orbits into duplicate points. The
   collinearity guard aborted it (exit 1, `runs/sphere_cubocta_12.*`). It is kept as is and not rerun.
6. **"Every chord direction is extreme" route.** For any secant direction u there are functionals (ζ, Λ)
   making u a vertex of the slope hull. This turned out to be vacuous: in RP¹ every point is adjacent to a gap.
   It gives no parity information. Same weakness as in the planar case, where all-even sets exist.
7. **Ak-type modification in 3-D.** Ruled out for a single swap on three layers (Lemma D). Multi-point
   modifications were not analysed.
8. **Two non-parallel planes, two-sided.** Zero divisors exist in F₂[R⋊R*]. The rank-one/extreme-row
   matching analysis is not closed (discovery.md, Prop B remark).
9. **Three parallel layers.** The leading terms force the vertex identity t₂−b₁ = (t₃−b₂)/(h−1) for every
   generic φ, which implies that K₁ and K₃ have the same difference body (h = 2). There is no contradiction at
   leading order. Collinear triples across layers make the count trilinear. Not closed.
10. **Equal-length parallel classes and high-dimensional cube/hypersimplex/root-type sets.** These die by the
    domain argument (ff^* = |S| impossible), so they cannot produce examples. This is a trivial
    singly-determined-direction argument with no credit.
11. **Prior-art screening.** arXiv API only (http.jsonl). There was no attempt at GitHub, ScienceDirect, Google
    or the live registries (denied or out of scope). No 403/429/challenge occurred.
12. **Verifier scope lapse (attempt 1).** The first verification bound the live administrative NEXT.md as if
    it were a scientific original. The root edited NEXT.md meanwhile (this lane never wrote to it), so the
    attempt reported FAIL. That receipt is preserved unchanged as `runs/verify-attempt1-FAILED-receipt.json`.
    The verifier now requires exact equality only for scientific originals (source PDF/abs, SCOUTING.md,
    guard) and records administrative drift without failing. The administrative snapshots in
    `admin-snapshot/` are the bound copies.
