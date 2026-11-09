# Residual formal obligations

None. The full endpoint passes both local strict checking and the fresh extracted strict replay.

Predecessor gap A is closed by `RACGNormal330264.clean_implies_reduced` and `reduced_iff_clean` in TraceAction.lean. Its permutation action is constructed from the actual presented-group universal property; every swap, cancellation and length bridge is proved.

Gap B is closed by `mem_frontState`, `suffixState_clique`, `suffixState_append`, `Machine.accept_context`, `accepts_iff_reduced`, `run_state_exact`, and `failure_iff_not_reduced`. The concrete machines discharge their transition specifications by finite kernel checks.

Gap C is closed by `splitWords`, `wordCount_succ`, `geodesicGrowth_eq`, and the checked concrete stages. The new backward recurrence counts individual accepted words for every length; at18 it certifies the same totals as the inherited forward recurrence. No source recognition assumption and no recurrence definition of geodesic growth is used.

Gap D is closed by `MathDB330264.counterexample` and `MathDB330264.conjecture_false`. Tree and actual triple-characteristic-polynomial proofs reuse preserved predecessor bytes.

Independent source/statement-fidelity and novelty/significance review, paper and root acceptance decision remain outside this formal closure. Zero acceptance credit is claimed here. The inherited primary comparison is bounded, not novelty clearance.
