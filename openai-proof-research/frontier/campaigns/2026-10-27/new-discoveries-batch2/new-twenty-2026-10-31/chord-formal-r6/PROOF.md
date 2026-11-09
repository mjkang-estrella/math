# Round 6 proof record

This is implementation work, not acceptance. None of the four original requested Props has an unconditional proof in this packet.

`Chord6Swap` strengthens the inherited disjunctive successor-swap theorem to an exact sign criterion for every finite permutation. First, suppression of a nonfixed Option point preserves and reflects SameCycle between retained points. This follows by mapping orbit steps through the inclusion and through a retraction sending the removed point to its successor. Inserting a point after a prescribed predecessor therefore preserves all retained connectivity.

The refined swap theorem inducts on the finite type size, moving the first attachment point to Option.none. When none is fixed, swapping merges its singleton cycle with the other cycle. Otherwise suppress none, retaining its successor a. If the other attachment's successor equals a, swapping splits off none. In the remaining case the smaller swap is at h.symm a and b; connectivity is precisely the original connectivity. This proves +1 for SameCycle and -1 for different cycles. Applying the result again to the swapped permutation proves that the swap toggles the two attachment points' connectivity.

`Chord6Split.innermost_distinct` gives a closed face explicitly in the frozen three-half-edge model. Write b = partner a with a < b. If c a is false, the closed set consists of C at a and P at positions a+1 through b. Its transitions are C_a to P_b, P_i to P_(i-1) through the opposite-colored interior, and P_(a+1) to C_a. This excludes C_b. If c a is true, the closed set consists of C_b and N at positions a through b-1, with the analogous forward transitions, excluding C_a. Finite SameCycle cannot leave a set closed under the face permutation. The proof uses literal theta/rho and includes adjacent endpoints.

Given BandErasure, the omitted pair for removeChord is the chosen monochromatic chord. The swapped count equals the restricted smaller boundary. Since its C half-edges are in different cycles, the refined swap theorem says the swapped count plus one equals the original boundary. This is exactly the unchanged MonochromaticSplit statement. No genus parity, dart model, or alternative boundary definition is assumed.

The planarity induction and round-5 odd-cycle theorem then yield BipartitePlanarity and TriangleReduction conditional only on BandErasure. The final intended endpoint uses BandErasure, EndEdgeSurgery and TriangleRigiditySix. The n=4 classification and n=1,2 refutation remain unconditional inherited theorems.

## Remaining work

1. BandErasure: prove simultaneous suppression of the omitted two bivalent backbone vertices, including the zero-chord annulus case (already certified separately). The exact local erased-face formula and omitted-pair identification are inherited, but a general compression certificate is still absent.
2. EndEdgeSurgery: inserting two adjacent vertices subdivides the old end-edge transitions. Equal sides introduce one additional closed face; opposite sides induce the successor swap at the end-edge half-edges. The new refined sign criterion and inherited EndSame/SameCycle identification supply the counting criterion, but the arbitrary-size insertion/compression transport remains to be formalized.
3. TriangleRigiditySix: transport each chosen triangle through the five-chord classification, then complete common-arc, adjacency, and dihedral reconstruction. The round-5 five-chord transport and triangle uniqueness do not by themselves prove that global argument.

MonochromaticSplit remains unproved without assumptions, but it is no longer an independent assumption once BandErasure is supplied. This distinction is recorded explicitly in results.json.

## Concrete end-edge compression route for continuation

For the appended endpoints p=2n and q=2n+1, only the old inputs P_0 and N_(2n-1) change their successors. For opposite sides c(p)=false,c(q)=true the new paths are

- P_0 → P_q → C_p → N_q → old f(N_(2n-1));
- N_(2n-1) → N_p → C_q → P_p → old f(P_0).

Thus suppressing the six new half-edges gives the old successor swap at the two end-edge inputs. Moreover P_0 and N_q are visibly on the same new cycle. For equal false sides the paths are P_0 → C_q → P_p → old f(P_0) and N_(2n-1) → N_p → N_q → old f(N_(2n-1)), with a separate 2-cycle C_p ↔ P_q. This adds one cycle and preserves the old end-edge connectivity. True/true and true/false are the mirrored cases. These transition lists are a continuation plan, not additional Lean theorems or closed EndEdgeSurgery claims.
