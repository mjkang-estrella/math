# Boolean-lattice cd-index screening

Research evidence only; discovery credit **0**.

The actual source is Mahajan, *The cd-index of the Boolean lattice*, arXiv math/0211390v1, Section7, Conjectures3 and4. The source PDF has SHA256 `1abd2d3cf281a963ff6c7762b8e0656284125e5c73240be9484af54fe4f99413`. Its actual coefficient recurrence and balance definitions were read.

`search_balance.py` independently rediscovered a degree25 counterexample to pair balancing: beta(0,5,0,7,5)=1287894857340 < beta(0,4,0,7,6)=1288645806880. The full live MathDB377680 solution was then inspected: **the same witness and values were already posted by Shivam Patel on August20,2026**, solution462061f2-edfa-46df-ba51-c269c1cbb51b. This is excluded from the campaign; rediscovery has no novelty credit. Snapshot: sources/377680-live.json.

`search_balanced_lists.py` searches the distinct weaker balanced-list question, MathDB377681. It computes all cd coefficients through degree30 (1,346,269 coefficients at degree30), but tests balanced middle lists of length at least3 with left and right contexts of length at most1 only. It found no violation in those finite restricted contexts. This is **not** a proof of the weaker conjecture or a general no-counterexample statement. The live377681 snapshot was open with empty solution/progress fields when fetched. Logs and exact JSON output preserve the limits of the searches.

No Lean proof, paper or accepted outcome is claimed for this lane. No external posting occurred.
