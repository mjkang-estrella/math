# Research holds only — no discovery nomination

## Rank 1: unrestricted zero-sum threshold

Li–Ling–Sun–Zhu, arXiv:2610.19965v1, submitted14 Oct2026, Question3.1 printed/PDF p15, https://arxiv.org/pdf/2610.19965v1. For every integer n>1 and r≥1, w_r(n) is the least N such that every length-N sequence of integer r-vectors, each nonzero modulo n, contains a nonempty subsequence whose sum is 0 mod n but not 0 mod n². The question asks w_r(n)=2r(n−1)+1. All lifts are allowed; a residue-zero subset summing to zero mod n² does NOT satisfy the target. This is a full all-r/all-n question, not a prime-only parameter instance.

The authors' actual Lemma3.1 gives the signed coordinate lower construction. Theorem1.2 covers rank1, all binary moduli, and rank2 for n=2^k3^l p. These own/public outcomes are not candidates here. Source v1 remains latest in the bounded API check. Original Sun2606.18234v5 is earlier (2July2026); the October successor refutes his fixed-length rank2 conjecture, so that older claim cannot be recycled.

Route A, strongest classical objection: their actual Lemma4.1 splits every bad sequence into two reduced residue subsequences B,C, giving w_r(n)≤2h((Z/n)^r)+1. Thus a classical h((Z/n)^r)≤r(n−1) theorem would immediately settle this question, with their lower bound; any such theorem must be body-checked before proposing novelty. The obtained Letzter–Morrison2306.09033v2, Theorem2.1 proof pp5–6, uses matroid base packing and an additive-bases theorem to prove h(F_p^r)≤(p−1)r(log_2 r+1), not r(p−1). Its conclusion p14 still asks even a 2p+O(1) rank-two bound. Dropping log_2 r is unsupported. For general composite n the successor gives a quadratic-r bound. Therefore this actual public bridge is incomplete.

First failed shortcut: reduced does not imply zero-sum-free, so a Davenport bound cannot simply be substituted. In Z/3, [1,−1] is reduced: its subset sums are {0,1,2}, and removing either term loses one value. Yet its two terms sum to zero. This is an exact method falsifier, not a refutation of the source question or of the desired bound on h.

Route B, pursued beyond that failure: fix prime p and nonzero residues a_i∈{0,…,p−1}^r. All possible lifts modulo p² are a_i+p b_i. For every nonempty subset I with Σ_I a_i≡0 modp, badness is EXACTLY the simultaneous linear equations
Σ_I b_i = −(Σ_I a_i)/p modp, coordinatewise.
Necessity follows by dividing the required mod-p² zero sum by p; sufficiency follows by reversing this calculation for every residue-zero subset. This is a complete finite bridge for fixed residues, not a universal structural theorem and not a discovery nomination. Gaussian elimination tests liftability, unlike directly enumerating p^(rN) lifts.

The capped executable checks test p=3,r=3,N=13: all26 one-term extensions of the fixed signed-coordinate length12 residue witness, then214 seeded random lists. All240 systems are inconsistent. This falsifies the attempted one-extra-term construction and those random instances ONLY. No counterexample or universal proof emerged. A rigorous local obstruction retained: four copies of residue1 mod3 cannot lift to a bad sequence, since each triple forces Σ triple b=−1, subtracting equations forces all b equal, then3b=−1, impossible.

Missing universal lemma for this route: for every prime p,r≥1 and N=2r(p−1)+1 nonzero residues, the displayed full subset-incidence system is inconsistent. This would only prove the prime-modulus portion; an additional all-composite lifting/induction theorem is required. Neither is established. A more direct missing full lemma is the desired length bound for all bad sequences; we do not disguise it as a proved reduction.

Next calculation: classify liftable incidence systems under GL(r,p) and position permutations, starting with rank-three p=3, and retain exact inconsistent-row certificates. A counterexample must supply a consistent system AND verify every residue-zero subset. A proof must control arbitrary rank and modulus, not the sampled systems. This deserves a research hold, not formalization or acceptance.

## Rank 2: Crazy Knight tours

Mella–Pasotti2311.09054v2, Conj2.3 printed p3, https://arxiv.org/pdf/2311.09054v2, update4May2026. Every cyclically k-diagonal n×n array has a row/column orientation whose horizontal-then-vertical move permutation is one nk-cycle exactly when n,k are odd and n≥k≥3. Diagonals are cyclic consecutive diagonals as defined in the source, not arbitrary subsets.

Complete strongest objection: Thm5.1, reduction Propositions3.6/4.13 and subsequent corollaries already provide extensive infinite classes, and Theorem2.4 propagates n by k−1 when an orientation side is uniform. Any cycle-splicing argument that only reproduces their gcd(g+1,k−1)=2 class, g=gcd(n,k−1), or their §5.4 construction is publicly subsumed. Eulerian connectivity alone does not supply one tour: all moves in a row/column must share an orientation. The source's concluding p20 explicitly retains exceptions among k≤245; numerical success on them would still not solve the universal statement.

Concrete mechanism: choose initially all row signs positive; reverse selected columns to splice the g residue cycles. A valid switch lemma must give the exact permutation on the induced transversal and prove that an admissible selection makes it one cycle for EVERY odd n,k, including gcd(g+1,k−1)>2. Source bishop reductions are the starting point, not a novelty claim. Next calculation is to derive the cycle-change formula for two column reversals with overlapping supports and compare it directly with §3 and §5.4; no such universal lemma is proved here. No finite instance nominated. Current public registry remains inaccessible; complete successor clearance absent.

No rank3: circuit-spindle question is too close to the circuit Hirsch barrier without a new mechanism. Magic rectangles were retired by an actual full successor. Neither rank is novelty-cleared or solved; no PROOF.md is appropriate.
