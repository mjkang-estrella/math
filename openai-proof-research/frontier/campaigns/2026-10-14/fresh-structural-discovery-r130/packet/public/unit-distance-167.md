# Family 167: planar unit distances, unbalanced incidences

This is a prefreeze feasibility calculation. It is not nominated, and it is not certified as a proof. It is recorded because it is the strongest compatible consequence I found. It is a classical compiler application, which the brief says earns nothing.

## Stipulated source contract (introduction read in full)

Pinned source *A power saving for planar unit distances*, `build/sections/00-introduction.tex`, `thm:main`: there are absolute 0<C<infinity and 1<=beta<4/3 with u(n) <= C n^beta for every n. Here u(X) counts unordered pairs of X at Euclidean distance one. The proof is by contradiction along a counterexample sequence and gives no explicit beta. Write beta = 4/3 - delta.

## Unbalanced bound by polynomial partitioning

For finite P, Q in R^2 with |P| = m <= n = |Q|, let I(P,Q) count pairs (p,q) in P x Q with |p-q| = 1. The proposed form is

    I(P,Q) <= C' [ (mn)^(2/3) (n/m^2)^delta + m + n ].

For m >= n^(1/2+eps) this is a power saving over the classical (mn)^(2/3). For m <= sqrt(n), the classical bound is already O(n).

Calculation (assuming m >= sqrt(n)):

1. Balanced input: I(A,B) <= 2 u(A union B) <= 2C(|A|+|B|)^beta, since each unordered unit pair yields at most two ordered pairs.
2. Take r = n/m >= 1 and a Guth–Katz partitioning polynomial f of degree at most r. There are at most C r^2 cells, and each contains at most s = n/r^2 = m^2/n >= 1 points of Q.
3. A unit circle S_p not contained in Z(f) meets Z(f) in at most 2r points (Bezout), so it meets at most 2r cells. The cell incidences total at most sum_i (|P_i|/s + 1) 2^(1+beta) C s^beta, with sum_i |P_i| <= 2rm. Chunking P_i into groups of size s is what makes the sum linear in |P_i|.
4. Points of Q on Z(f): circles not in Z(f) contribute at most 2rm. Circles contained in Z(f) are irreducible components of degree two, so there are at most r/2 of them. The classical unit-circle Szemeredi–Trotter bound then gives O(r^(2/3) n^(2/3) + r + n).
5. With rm = n and r^2 s = n, the total is O(n s^(beta-1) + n + r^(2/3) n^(2/3)). The first term equals (mn)^(2/3) (n/m^2)^delta. The last term equals (mn)^(2/3) (n/m^2)^(2/3), which is smaller because n/m^2 <= 1 and delta < 2/3.

Symmetry I(P,Q) = I(Q,P) covers m > n.

## Why this stops

Every step is a standard divide-and-conquer amplification of a balanced incidence bound (Clarkson–Shor/Guth–Katz partitioning). The source contract is used only as a black box at one point. No integrated operation remains unpaid. The source's own contradiction argument may also give the bipartite form directly. That was not checked, because only the introduction was read. Two other directions were rejected before any calculation:

- Unit distances on a 2-sphere of radius not equal to 1/sqrt(2), and planar unit distances for other algebraic norms, change the jump relation (z_p - z_q)(w_p - w_q) = 1 on which the source's height and product-formula steps rest. Transferring them would mean redoing the whole proof. That is an unbuilt central step, not a closable compatibility.
- Weak pinned and distinct-distance corollaries belong to the companion and to structural r42's pinned higher-dimensional target. They are not reopened.

No exact target was frozen.
