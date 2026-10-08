# H014 preflight — raw Opus report, root qualifications pending

2026-10-08. Read-only independent review, no numerical run. Its p43 obstruction
and parity-control objection require pre-run revisions. Runtime/admission
estimates and some universal statements are not accepted without qualification.

**Verdict: reject the protocol as written; approve with conditions.** It has one deterministic failure. As frozen, the protocol produces no data: p=43 cannot pass admission, and its stop rule would end the run there. It also has one confound that changes what an output means. The ring arithmetic, characters and identity controls are sound. All checks below are by hand and on paper; I ran nothing. The root should verify the trace and class-number arithmetic before freezing.

## A. Admission fails for certain at p=43

- **Why p=43 has no admissible curve.** Hasse allows q in [30.9, 57.1]. The only primes ≡7 mod 12 in that range are 31 and 43, and 43=p is excluded. q=31 means trace t=13, so t²−4p = −3. The only order of discriminant −3 is Z[ω], so j=0 and a=0, which the a≠0 rule excludes. Field 1 must fail, and under "stop incomplete, no replacements" the whole test ends with zero signal data.
- **p=101 is likely to fail too.** The only admissible q is 103 (t=−1, D=−403, h(−403)=2 by hand reduction of forms). By the standard count, a random pair has that trace with probability about H/(2p) ≈ 1%.
- **p=251 is in the same position.** The admissible q are 223, 271 and 283, with D = −163, −643, −43 and H ≈ 1+3+1. That also gives a hit rate near 1%.
- **What that means for a 64-pair window.** For both fields the 64 pairs are just a=1, b=1..64, so P(hit) is only about 0.5 by heuristic. That window is not random, so treat 0.5 as a rough figure.
- **Smallest fix, made before freezing.** This is a design change, not a post-hoc replacement, because nothing has run.
  - Drop p=43 and record why it is inadmissible on paper.
  - Treat each field's admission independently: a failed field is recorded, and the other field still runs.
  - Raise the window to about 256 lex pairs (expected hits ≈2.5 per field). Count it against the cap: roughly 256·(101+251)·4 ≈ 360k events if the x³ table is shared per field and charged. Don't use 512 pairs; with full charging that comes close to the 1M cap.
  - Any added field needs this same paper check before freezing: admissible t, and D not equal to −3 or −4.

## B. The permutation null is miscalibrated by about √2

Both features are odd. y-sign is odd because center_p(−y) = −center_p(y). fpar is odd because chi6(−c) = −chi6(c), since h is odd. chi6 is odd too, so the n and −n terms of the sum are identical. The sum therefore has (q−1)/2 independent terms, doubled.

A full Fisher–Yates shuffle of F breaks that pairing, so its null is about √2 too small, and that inflates any apparent signal. **Fix:** shuffle values over the half-representatives {1..(q−1)/2} and extend each permutation oddly. Keep seeds 7, 19 and 43, and keep all outputs.

Also pin down the PRNG and the method for drawing bounded integers in the frozen text. The exact algorithm plus rejection sampling is enough; "seeded" alone is ambiguous across libraries.

Optional: the exact null second moment for an odd-preserving random permutation has a closed form in Σ|a|², |Σa|² and Σ_R chi. That would be a better reference than three draws.

## C. Ring, characters and controls check out

- **Z[ζ] arithmetic.** ζ²=ζ−1 is correct (minimal polynomial x²−x+1). conj ζ = 1−ζ, the product rule is (a+bζ)(c+dζ) = (ac−bd) + (ad+bc+bd)ζ, and |a+bζ|² = a²+ab+b². Every summand lies in μ6 ∪ {0}, so the sums are exact.
- **Choice of g is harmless.** Changing g only swaps chi for conj chi. For real y-sign that conjugates c. For fpar, the feature and the target both conjugate, so |c| is unchanged. Freeze the mapping zeta_field^j → ζ^j, add the check chi6(g)=ζ, and compute fpar only against chi (not chi^5).
- **Choice of G is harmless.** Base invariance means |c| does not depend on G, so taking the lex-first point creates no selection freedom.
- **Why q≡7 mod 12 must stay.** If h were even, chi6 would be even and both odd features would give c=0 exactly, a forced null.
- **Why the j=0 exclusion must stay.** With j=0, the automorphism (x,y)→(βx,y) acts as a cube root of unity mod q and fixes y. That would force exact cancellation for y-features against chi6. j=1728 is irrelevant here because q≡3 mod 4.
- **Controls.** The expected exact values are:
  - S(2G) = chi6(2)·S
  - S(−G) = −S
  - planted S = q−1

  The −G check is weak because odd features pass it by construction; it only exercises negation. 2G is the meaningful arithmetic check, so compute it by actual point arithmetic, not by reindexing.
- **Detection floor.** The null scale is about √(2/(q−1)): roughly 0.14 at q=103 and 0.09 at q≈250. With two curves, only a gross correlation (|c| ≳ 0.3–0.4) can stand out. Freeze a descriptive threshold, for example |c| > 3× the null RMS, labelled "gross structure, warrants analytic look". This test cannot contradict q^{-1/12}-type prior art, which is vacuous at these sizes anyway.
- **fpar caveat.** −x/y is the formal-group parameter. The intuition that [n] scales it by n belongs to anomalous curves (Smart's attack) and does not carry over when q≠p. That gives fpar a low prior, but it is no reason to exclude it. When q < p (q=223), reduction mod q is not injective on (−p/2, p/2); this is harmless.

## D. The √3 rationale does not survive the backend cost

- **Where the √3 comes from.** Because h is odd, chi6 = (sign character chi2) × (cubic character chi3). The chi2 part only repeats the negation map, so the whole √3 cardinality factor comes from chi3.
- **Why fewer candidates isn't less work.** Coset steps are multiplicative: baby steps [λ^a]G and giant steps [λ^{-bB}k0^{-1}]Q are fixed-base scalar multiplications, not single additions. Even with a perfect, free chi6 oracle, beating rho-with-negation needs 2√(h·v_G·v_Q) < s·0.886√q. That is √(v_G·v_Q) < 1.085·s; against BSGS-with-negation the bound is still about 1.73. A fixed-base comb reaches v≈1 only with w ≈ log₂q, which means tables of size about q. This matches the raw proposal's own threshold m ≳ (2.3·log₂q/w)², which m=6 misses at any meaningful q.
- **This is not a theorem.** It holds only "under known coset backends". A constant-addition coset step, or a cheap endomorphism acting as λ, would reopen it. Excluding j=0 removes the only obvious such endomorphism.
- **Smallest fix: relabel the test.** Call it a qualitative probe of whether explicit public coordinate features correlate with multiplicative characters of the log at all. Drop the "potential √3 gain" framing. Cpre < s·W0 for the full feature-plus-backend pipeline stays the binding gate. Even with free estimation it already requires s > 1/√3 plus backend overhead.

## E. Accounting is minor

The total is well under the cap: about 10k events per curve for enumeration ×3, features, exponentiations, planted control and permutations, plus admission (A). Charge the shared x³/squares tables and the six-entry ζ table once per field, and report each field's partial totals.

## Prior disagreements I'm keeping

- The claim that order-2 oracles are useless is not a theorem. BBUV gives algorithmic upper bounds, not lower bounds.
- Generic and Weil-type bounds are not coordinate-aware for non-algebraic features such as y-sign and fpar.
- The no-gain point in D is likewise "under known backends", not a theorem.

**Approval conditions:**
1. Drop p=43 on the paper argument above.
2. Run admission per field over a window of about 256 pairs, fully charged.
3. Use odd-preserving permutations.
4. Freeze the PRNG, the ζ mapping, and computing fpar against chi only.
5. Pre-declare the descriptive threshold.
6. Relabel the test as a qualitative probe, not a √3 channel.

Nothing here demands a correlation proof first.
