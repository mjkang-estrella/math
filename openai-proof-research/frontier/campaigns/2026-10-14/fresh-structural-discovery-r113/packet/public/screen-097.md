# 097 — colorful rearrangement is explicit upstream

The contemplated direction was a square-root-dimension bound for synchronous aggregate prefixes of an arbitrary number of vector rows, with only their global total sum zero. This was screened before freezing.

The source's `thm:signing` gives one prescribed-order signing for all prefixes, norm ≤C√d, with no sequence-length dependence. Its `cor:colorful-steinitz` in `consequences.tex` already states the entire contemplated row-permutation conclusion: for k rows each of length n, unit Euclidean entries and total sum zero, one tuple of row permutations makes every synchronous aggregate prefix at most 2C√d, independently of k and n. Its proof first flattens an arbitrary array in column-major order to bound the signed matrix constant V, then applies U≤2V. The same section pays the stated ℓ_p norm-comparison variants. No online or polynomial-time construction is in these contracts.

The actual primary is Bárány, *A matrix version of the Steinitz lemma*, [arXiv:2308.10102v2](https://arxiv.org/pdf/2308.10102v2), Lemma 2.1 and Theorem 2.2 with §3 proof. Pair adjacent entries in each row, sign their half-differences, and place the selected entries at opposite ends. For an optimizing array the new prefix norm is at most U/2+V, forcing U≤2V. The odd-column ending is also included in the inspected proof. Source097 expressly uses this exact transference, not merely a weaker abstract vector theorem.

Thus there is neither a missing simultaneous-row selection operation nor an uncharged dependence on k in this proposed consequence. Requiring separate control of each row, unequal clocks, an online rule, or an efficient algorithm would change the contract and would need separate work; none was silently added or claimed. No nominee.

Historical body comparison also found the explicit colorful exclusion in the earlier r4 source-contracts note, I134's two-order-prefix development, and r44's constrained tree-signing work. The relevant passages were inspected; those constructions were not restarted or presented as new here.
