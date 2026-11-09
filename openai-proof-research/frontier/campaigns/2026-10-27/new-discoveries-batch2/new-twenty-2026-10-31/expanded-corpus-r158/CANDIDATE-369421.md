# Candidate 369421: a 3-representation of the 3-by-5 toroidal grid

Full literal Lean refutation, pending root review. Zero accepted credit here.

The target is Alshammari–Kitaev–Pyatkin, arXiv:2507.16469v1, Section 4, Conjecture 1 (PDF page 10): for m,n >= 3 and m+n >= 8, the representation number of C_m square C_n is at least 4. The current abstract page lists v1 only. The paper defines uniform word-representation using alternation of the subword induced by each pair of distinct letters. This is a human-posed conjecture.

## Certificate and ordinary proof

Label (r,c) by 5r+c, for 0 <= r < 3 and 0 <= c < 5. The word is

    0 8 4 5 9 11 12 13 10 1 2 6 11 0 1
    14 5 10 3 4 7 0 8 9 6 5 12 11 2 1
    7 6 13 12 3 2 8 14 10 13 4 3 7 9 14

Every letter occurs three times. For each unordered pair a,b, delete all other letters and check that successive remaining letters differ. This is true exactly for the 30 edges of C3 square C5: same row and cyclically consecutive columns, or same column and different rows. It is false for all other 75 pairs. Hence the word is a 3-uniform representation and the representation number is at most 3. Since 3+5=8, Conjecture 1 is false.

The complete pair certificate is outputs/pair-certificate.json. An independent positional checker verifies the equivalent two strict six-position interlacing orders. It agrees with the adjacent-filter checker on all 105 pairs. No claim that the representation number equals 3 is needed.

## Formal endpoint and replay

lean/Definitions.lean defines vertices as Fin m × Fin n, Cartesian cycle adjacency, pair filtering, successive alternation, k-uniform representation, and the least positive representation number (infinity if none exists). There are no surrogate graph predicates or bounded conjectures.

lean/Witness.lean proves Toroidal.witness_represents, Toroidal.number_le_three and Toroidal.mathdb_369421 : not Conjecture1. The first theorem uses kernel decide. The minimum bridge uses Nat.find_min'. The full universal conjecture is specialized at (3,5).

lean-packet.tar.gz contains exactly Definitions.lean, Witness.lean and Audit.lean. It was freshly extracted into extracted/ and strictly rebuilt in extracted-replay/. All three modules passed explicit-module leanchecker. The audit checks all 23 local declarations, including generated declarations, for forbidden metadata and every declaration's transitive axioms. Only propext, Classical.choice and Quot.sound occur. See outputs/lean-sha256.txt and extracted-replay/logs/.

Reproduce with scripts/replay.sh NEW_EMPTY_REPLAY_DIRECTORY EXTRACTED_SOURCE_DIRECTORY, both inside the authorized lane. The scripts use the prescribed Lean 4.34.1 binary and pinned read-only mathlib. Cached upstream oleans are trusted; no full upstream source rebuild is claimed. The process wrapper applies the requested caps. A PATH shim gives -M3500 to leanchecker-spawned Lean calls too.

## Search and coverage

scripts/grid-cnf.py creates pairwise ordering variables for 45 letter occurrences, strict total-order transitivity, ordered copies of each letter, interlacing constraints for edges, and failure of both interlacing orders for nonedges. Rotation symmetry fixes the first occurrence of 0 at the start. The resulting instance has 1020 variables and 28904 clauses. CaDiCaL returned SAT. scripts/decode.py reconstructs and independently checks the word. Lean does not trust the solver.

Only the first new toroidal case (3,5) was needed. No general-family claim is made.

## Source and prior-art gates

The source's Sections 2–3 give 3-representations for grids and cylinders; neither includes wrap edges in both coordinates. Section 4 supplies smaller toroidal examples (3,3) and (3,4), then explicitly says larger 3-representations are unknown. Its Figure 2 illustrates (3,5), ruling out a hidden order convention. The theorem statements and relevant construction proofs were read.

Broere–Zantema's downloaded product theorem, arXiv:1808.01800, gives (k+n-1)-representability for product with K_n. Applied to C5 and K3 it gives 4, not 3. Broere's 2018 thesis was downloaded and relevant cycle/prism/cube/product sections examined; no certificate for this graph was located. Hefty–Horn–Muir–Owens, EJC 31(4) (2024), #P4.2, was downloaded and the relevant poset/cube results examined; these do not supply this nonbipartite 15-vertex graph.

The newer same-author paper Kitaev–Pyatkin, Acta Informatica 63:33 (18 September 2026), was read in its relevant introduction and rook/queen proof sections. It distinguishes toroidal and rook graphs. Its 3-representation theorem for rook graphs concerns two rows; the larger rook graphs do not give this result by edge deletion. No printed representation of C3 square C5 was located there.

The credited families and exclusions 337352, 347138, 355701, 341250 and 373598 were considered. This is an independently written literal SAT model, not a short augmentation/sparsification of a printed obstruction. The source gives no SAT/enumeration procedure which this merely runs on its next catalogue entry. The newer companion mentions a failed computer search on a different rook graph, not a construction for this target.

Live proof registries were refreshed: OpenAI/math HEAD 4eaee87548250b2682affda7d05d947c05554bae; Omega HEAD 2c54932b6f9a7eb9a838e5be71e91d97e10027be. Complete OpenAI preprints and Omega D5/Problems subtree listings were obtained without truncation. The root recursive trees were truncated and were not treated as complete. Path/topic screens found no matching proof. This is a bounded screen, not reading every proof body.

Dated public queries included the source ID/title, toroidal 3-representation, exact C3/C5 products and 2026 counterexamples. No prior certificate was located. Historical ID/title screens are retained in outputs/history*.txt. Literature novelty is a bounded nonfinding, not a theorem.

## Retention qualification

Kitaev's publication list, entry 176, identifies the paper as to appear in Journal of Automata, Languages and Combinatorics and links its PDF directly to arXiv:2507.16469. The university repository records acceptance on 26 February 2026, retains the abstract's reference to the toroidal conjecture, and links arXiv as the access document. The current arXiv PDF retains the exact Conjecture 1.

This is positive author/institutional linkage to the accepted paper. The accepted-author manuscript is staff-only under a 2099 embargo and was not accessed or read. Exact accepted-body retention therefore remains qualified for root. No access bypass or author contact was attempted.

No independent adversarial review, root acceptance or campaign manuscript is claimed. Root should review fidelity, significance, prior art and the retention qualification before counting this.
