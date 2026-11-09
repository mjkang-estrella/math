# MathDB 342364: final statement correspondence

The primary source is Ulas–Żmija, arXiv:1904.03398v1, Conjecture 6.1, cached in ../expanded-corpus-r130/sources/1904.03398v1.txt, lines 1729–1735. The definitions are at lines 125–151 and 183–186. This assembly makes no new prior-art or novelty clearance claim; the independent review and its access limitations remain relevant to root's decision.

The source defines C(x) = (1−x)⁻¹ ∏_{i≥0}(1−x^(2^i))⁻¹ and c_m(n) = [x^n]C(x)^m. UlasSeries defines geomStep, the finite product G, its coefficientwise stabilization C, and literally c m n := PowerSeries.coeff n (C^m). G_agree, coeff_G_stable, C_agree and c_eq_finite establish stability for arbitrary powers. There are two factors at part size 1: part 1 has 2m colours, while each part 2^i, i ≥ 1, has m colours. This is the source convention, not the usual m colours at every size.

All statement definitions below are the inherited byte-identical definitions in UlasFinal.lean. The new module defines no replacement Props, coefficients, valuations or sets. Ulas.diff m n = c m (4*n) − c m n, and Ulas.val m n = padicValInt 2 (diff m n).

Ulas.Final5.full_theorem_E2 proves the conjunction of the following frozen statements without hypotheses:

- EvenFormula: for every k ≥ 1 and n ≥ 1, diff (2*k) n ≠ 0 and val (2*k) n = ν₂(n) + 2ν₂(k) + 3.
- OddOneBound: for every k ≥ 0 and n ≥ 1, diff (4*k+1) n ≠ 0 and val (4*k+1) n ≥ ν₂(n) + 3.
- OddThreeBound: for every k ≥ 0 and n ≥ 1, diff (4*k+3) n ≠ 0 and val (4*k+3) n ≥ ν₂(n) + 6.
- OddOneEquality: equality in the +3 bound for every odd positive n, for every k ≥ 0.
- OddThreeEquality: equality in the +6 bound for every odd positive n when 4k+3 is 3 or 7 modulo 16, and for every positive n congruent to 2 modulo 4 when 4k+3 is 11 modulo 16.
- FifteenBound: for every t ≥ 0 and n ≥ 1, diff (16*t+15) n ≠ 0 and val (16*t+15) n ≥ ν₂(n) + 7.
- NeverFifteen: for every t ≥ 0 and n ≥ 1, val (16*t+15) n ≠ ν₂(n) + 6.

The nonzero clauses avoid the convention padicValInt 2 0 = 0. Equality families are explicit sufficient infinite sets, not iff descriptions. In particular the review records additional even equality points for m = 3; claiming that only odd n give equality would be false. The never statement for m congruent to 15 modulo 16 is universal and exact. This limitation is inherited from the reviewed manuscript and frozen definitions, and is disclosed for root's assessment of the ruling's phrase “exact equality sets.”

P1 is the per-k reading: Ulas.Conj61 retains the three universal valuation statements and requires all three equality sets to be infinite for each eligible k. Ulas.Final5.mathdb_342364 proves ¬ Ulas.Conj61 by the frozen refutation: k = 3 in the 4k+3 clause gives m = 15, whose equality set is empty by NeverFifteen.

P2 is the some-k reading: Ulas.Conj61Some retains the universal bounds but asks for one eligible k in each infinite sharpness clause. Ulas.Final5.conj61_some proves it, using k = 1 for even colours and k = 0 for each odd family. Arbitrarily large positive odd n supply the latter witnesses. Restricting the source's final n ∈ N to n ≥ 1 removes at most one point and preserves infinitude.

The assembly applies frozen Ulas.full_theorem to ⟨Ulas.Even5.evenFormula_proved, Ulas.Round5Odd.odd_theorem⟩. The same proved conjunction supplies frozen Ulas.mathdb_342364 and Ulas.conj61_some. The exact even theorem namespace in the archives is Ulas.Even5, correcting the abbreviated Ulas.evenFormula_proved in TASK.txt. Thus the full theorem resolves the source and MathDB claim under both readings: P1 is false and P2 is true. Acceptance, substantive credit, and independent final review belong to root.
