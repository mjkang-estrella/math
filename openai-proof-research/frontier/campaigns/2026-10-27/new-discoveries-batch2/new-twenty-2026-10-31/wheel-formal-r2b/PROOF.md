# Upper bound and final equality

Write m = 2t + 1 and D = 2t² + t + 1. The inherited graph has vertices Option (ZMod m) squared; none is the hub. Its edges are exactly the Cartesian product edges. Fractional colourings assign nonnegative real weights to every independent finite vertex set. The fractional chromatic number is the infimum of their total weights.

The new predicate alternating t x means x.val < 2t and x.val % 2 = 0. Its t members are the residues 0, 2, ..., 2t − 2. UpperCycle proves that no two members are cyclically adjacent. It also proves that after deleting a residue a, the parity of (i − a − 1).val changes across every surviving edge, including the proof that a surviving coordinate cannot have representative 2t in this numbering.

F0(s) consists of the hub pair and rim vertices with alternating t (i − j − s). UpperFamilies proves independence in the literal wheel-square graph. For any fixed rim vertex, subtraction by the translation parameter permutes ZMod m, so precisely t shifts contain it.

F1(a,b,c) uses c in Fin 2, equivalently the two Boolean colours. It contains the mixed vertices (a,hub), (hub,b) and the nondeleted rim vertices with ((i − a − 1).val + (j − b − 1).val) % 2 = c.val. The deleted-parity lemma proves independence. For each surviving pair of coordinates exactly one colour selects it. Thus the number of indices containing a rim vertex is (m − 1)² = 4t². Each mixed vertex belongs to 2m indices.

F2(a,b) has the alternating translates in the mixed layers. In the rim it selects coordinates that are both nondeleted and for which being the last representative (2t) is equivalent. The nondeleted nonlast coordinates are the t odd representatives; these are S and P1 in the assignment. The last representative is P2. Hence the selected pairs are exactly (S,S), (S,P1), (P1,S), (P1,P1), (P2,P2). Between nondeleted adjacent coordinates, the last-representative flag differs. This proves independence and handles t = 1 uniformly. Subtraction permutes residues, giving t ordinary-role translations and one final-role translation. The rim coverage count is t² + 1. Each mixed vertex belongs to tm indices.

Give every F0 index weight 1/m, every F1 index weight 1/(2mD), and every F2 index weight 1/D. The F1 weight equals the assignment's (m/D)/(2m²), since m is positive. Hub coverage is 1. Mixed coverage is 1/D + tm/D = 1. Rim coverage is t/m + 2t²/(mD) + (t² + 1)/D = 1. UpperAttaining proves these equations directly in Lean for every natural t. Repeated independent sets cause no problem: UpperIndexed sums all corresponding index weights to obtain a literal FractionalColouring.

Total weight is 1 + m/D + m²/D = (6t² + 7t + 3)/D. Applying fracChromatic_le_total yields the upper bound. The unchanged r2a theorem wheelSquare_fractional_lower supplies the opposite inequality for t >= 1. Final proves wheelSquare_fractional_eq and target_proved : WheelFormal.Target without additional hypotheses.

This is an implementation of the assigned ordinary proof and explicit construction. It does not independently establish novelty, significance, source eligibility, or root acceptance. The bounded prior-art findings and their limitations are preserved verbatim in inputs/wheel-formal-r1/PRIOR-ART.md.
