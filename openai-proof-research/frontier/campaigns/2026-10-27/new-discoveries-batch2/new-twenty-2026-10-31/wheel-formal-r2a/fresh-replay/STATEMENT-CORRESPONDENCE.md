# Statement correspondence

| Obligation | Lean declaration | Literal scope |
|---|---|---|
| Odd-cycle independence | WheelFormal.cycle_independent_card | Every natural t >= 1 and independent finite subset of ZMod (2t+1), card <= t |
| Near-perfect cyclic pairing | WheelFormal.cyclePair_spec | Involution fixing only zero; all other pairs are rimAdj edges |
| Deletion matching | WheelFormal.cycle_deletion_pairing | Every nonempty deleted set A, involution on its complement, adjacent nonfixed pairs, at most card(A)-1 fixed vertices; independence of A is unnecessary |
| Product matching bound | WheelFormal.deletion_grid_bound | Every independent finite I in the actual product of the two cycle complements, 2 card(I) <= (m-a)(m-b)+(a-1)(b-1) |
| Weight bookkeeping | WheelFormal.weight_profile | Exact sum of r1 vertexWeight over any wheel-square finite set |
| Mixed independence and rim avoidance | WheelFormal.mixedA_card, mixedB_card, rim_avoids_mixed, rim_grid_independent | Derived from r1 Independent on r1 wheelSquare |
| Hub and one-sided fibre bounds | WheelFormal.rim_row_bound, rim_column_bound | Uniform bounds on rimSet by surviving cyclic fibres |
| Universal weighted bound | WheelFormal.vertexWeight_independent_bound | For all t >= 1 and all s with Independent (wheelSquare t) s, weight <= 2(2t²+t+1), with no combinatorial hypothesis remaining |
| Fractional lower bound | WheelFormal.wheelSquare_fractional_lower | For all t >= 1, (6t²+7t+3)/(2t²+t+1) <= fracChromatic (wheelSquare t), using r1's literal fractional colouring infimum |

The source ordinary proof is the read-only WHEEL-PROOF.md in inputs. The definition bridge is inherited unchanged from r1. No upper bound, equality, or novelty clearance is claimed. The pairing proof replaces r1 GAPS items 2-3 rather than proving the optional component-decomposition statements. The product pairing first uses nonfixed column pairs, then row pairs in fixed columns.
