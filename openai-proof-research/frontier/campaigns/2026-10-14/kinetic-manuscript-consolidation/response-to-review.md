# Response to manuscript review N1-N7

All seven nonblocking corrections are applied. The prior full-scope PASS refers exclusively to the frozen original. Consolidated bytes await parent/focused review; no gate, acceptance or count is advanced.

## N1: Our right-continuous convention; fixed-time null event

Current `main.tex` lines 108-117. Adopt post-collision values at collision instants without attributing that convention to H. Conditional on each finite N, the initial law is absolutely continuous; contact lies on finitely many codimension-one surfaces, and measure preservation makes its fixed-time preimage null. Sum over N, with N=0,1 trivial. All fixed-time inputs are unchanged.

## N2: Pinned H shorthand, title and actual section mapping

Current `main.tex` lines 191-217. Read the actual first section command in every file and main.tex inclusion order. H05 is Section 7, H06 Section 5, H07 Section 6; the other indices equal their section numbers. The paper includes filenames, section numbers and exact titles. source-sections.json carries hashes and upstream paths.

## N3: Public-paper credit and internal process history

Current `main.tex` lines 1177-1180. Remove both opaque I340 mentions and all internal PASS/SUBSTANTIAL process prose from the paper. Explicitly credit the earlier Gaussian-continuity and uniform-centering deductions as inherited; identify their exact archived notes and sections in provenance.md and source-map.*. The scope discussion at lines 1273-1279 repeats that these are not new results. Internal review status stays in package documentation.

## N4: Consistent distinct notation

Current `main.tex` lines 1059-1079. Use p only for the particle index in the microscopic count argument; use j for factorial-moment order and h for root/block cardinality. Reserve d for test-vector dimension: displacement d_p becomes delta_p, deficit d_i becomes nu_i, polynomial degree d_K becomes gamma_K at every occurrence. Replace every bare tail target M by q_tail, including all threshold and exponent occurrences; retain M_i and M_phi. Additional current locations: tail definition and summability at lines 410-417; spatial offsets at lines 589, 676; deficit and degree at lines 801-817; pulse accuracy at lines 884-416. The original E3 distinctions (V, b, q/P, eta_0/eta, theta/vartheta) remain.

## N5: Fixed record-bound dependence

Current `main.tex` lines 336-362. Add r_rec to both O and C subscripts in eq:factorials. Define it as the fixed record bound and map it explicitly to H04 parameter m. Use the same r_rec notation in eq:coarse; avoid collision with the manuscript birth-line count m.

## N6: Pulse wording

Current `main.tex` lines 256-257. Replace the duplicated fixed-pulse wording with updates at prescribed pulse times. The proof retains its uniformity in arbitrary moving pulse locations.

## N7: Supremum tightness in Lemma 8.1

Current `main.tex` lines 1155-1173. State the probability double limit, then prove sup_t|Y_t| <= |Y_0| + ceil(T/u) w(Y,u). For any error tolerance choose u using the double limit with threshold 1, keep that u fixed, and use initial tightness to obtain a finite supremum bound. This supplies the extra hypothesis of JS VI.3.26 without changing any moment assumptions.

## Preserved scope and earlier repairs

The exact source assumption, excluded-product law including N=0, mu=epsilon^-2, unsmoothed whole-space deterministic flow, full supplied lifespan, exact microscopic centering, arbitrary finite C_c^infinity test lists, and J1 plus C-tightness conclusion remain intact. `references.tex`, inherited finite support programs and license files are unchanged. Exactly nine scoped Lean declarations remain support only; no full formalization is asserted.

E1-E7 and the proof-r1 chronology, all-line energy/Gaussian budget, decorated kernel/component inversion, exact Count error, and uniform-topology repairs remain intact. Current exact locations are in `source-map.*`; the original response is preserved in `history/editorial-response.md`. `original-to-consolidated.diff` is the complete, exact original-to-current TeX diff. No frozen original or release file was written.
