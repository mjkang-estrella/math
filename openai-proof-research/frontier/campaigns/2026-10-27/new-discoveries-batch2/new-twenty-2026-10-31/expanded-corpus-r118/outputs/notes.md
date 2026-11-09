# r118 working notes (ID-keyed)

## 358922 PD_2 dyadic congruence (Sellers arXiv:2306.15130, closing Conjecture)
- Source conjecture (main.tex l.910-913): for all k>=0, n>=0, PD_2(2^{k+2}n) == PD_2(2^k n) (mod 2^{k+1}). Based on computational evidence.
- Own check: scripts/pd2.c (via leanc), coefficients mod 2^64 to N=2^20; no failure for k<=18 (logs/pd2-1M.log). min v2 of difference = k+1 at k=6, so modulus is sharp there.
- PRIOR ART (read theorem body): Chern & Sellers, arXiv:2308.04348 (Acta Arith. 215 (2024)), Theorem 1.1: PDO(2^{2k+3}n) == PDO(2^{2k+1}n) mod 2^{2k+3}, all k,n; Corollary (n -> 2n): PDO(2^{2k+4}n) == PDO(2^{2k+2}n) mod 2^{2k+3}. PDO = PD_2.
  Odd k=2j+1: Thm gives mod 2^{k+2}. Even k=2j+2: Cor gives mod 2^{k+1}. k=0: Sellers' own internal congruence PDO(4n)==PDO(n) mod 4 (quoted in Chern-Sellers l.130-135; Sellers Thm internal_cong_mod4).
- Disposition: KNOWN full scope (published resolution). Stop.

## 358812 log-concave maximal parabolic seaweeds (Mayers-Russoniello arXiv:2306.10154, Epilogue conjecture)
- Spectrum calculator scripts/seaweed.py (oriented meander, source Thm thm:specmeander); reproduces the source's printed spectra of 2|4/1|2|3, 3|1/4, 3|2|2/4|2|1, 8|8|8|1/25.
- Sweep: all a|b/n and n/a|b with gcd(a,b)=1, n<=110 (5228 cases): log-concave, no internal zeros.
- Prior/partial: Coll arXiv:2609.27153 (2026-09-22): strict unimodality for all; log-concavity proved for W(mb±t,b), t<=3, and verified for smaller block <=128 with no bound on larger block; unrestricted conjecture stated open. Any counterexample needs min(a,b)>=129.
- Lean: would need Frobenius/principal-element semantics; not pursued. PARKED.

## 358810 parity-dependent spectrum for 2k|...|2k|1 / 2kr+1 (same source, Conj conj:stab2)
- Sweep k,r with n=2kr+1<=130 (272 cases): Frobenius, distinct-eigenvalue interval as conjectured, unimodal. Multiplicities grow irregularly with r (data in notes); no closed form found; literal Lean needs Lie-algebra spectrum semantics. PARKED.

## 359740 prime-order even-list conjecture (Meszka-Pasotti-Pellegrini arXiv:2308.16553 = Discrete Math 347 (2024) 114182, Conj conj:3)
- Necessity is the source's Prop prop:EvenNumber (parity count). Sufficiency open; source cites only "some computational results", no range.
- Exhaustive (scripts/seating*.c via leanc): all lists for p=3,5,7,11,13 (orbit-reduced by odd units of Z_2p): all realizable. Control p=9 (nonprime) finds 4 non-realizable orbit reps.
- Support-size-3 lists exhaustive for p=17,19,23: all realizable (budget misses resolved via unit images).
- No counterexample; no proof route. PARKED.

## 359279 multiset reconstruction n>=k+4 (Erickson-Herden-Meddaugh-Sepanski-Hammon arXiv:2307.13161, Conj conj:k+4; authors verified k<=5)
- Convention: mM_k counts all n(n-1)...(n-k+1) deletion sequences (source proof of thm: exp lower bound).
- scripts/minors.py (dense, n<=10) and scripts/minors.c (random linear hashes, n<=15) agree; reproduce source facts (k=1 sets n>=5; k=2 sets sharp n>=8; mM_2 injective n=6,7, not 5).
- RESULT: n=k+4 injective for k<=7 (k=6,7 new), FAILS for k=8 (n=12; 4 colliding rows = 2 pairs + transposes), k=9 (16), k=10 (60), k=11 (190). n=k+5 injective for k=8,9,10.
- Minimal counterexample: hooks T1 = rows [1,5,7,8,12],[2],[3],[4],[6],[9],[10],[11] (shape (5,1^7)), T2 = [1,2,3,7,10,11],[4],[5],[6],[8],[9],[12] (shape (6,1^6)); exact independent Python check: equal multisets of all 19958400 8-minors.
- Prior art: web searches (no follow-up resolution), 2025 Herden seminar slides and abstracts (only k=2 and cubic bound), Omega HEAD 0561ac6 complete D5/Problems path screen (no tableau-minor item), OpenAI/math HEAD 4eaee875 unchanged, cached preprint listing screen negative.
- LEAN: lean/TabMinors.lean, theorem TabMinors.not_conjecture : ¬ Conjecture; strict -DwarningAsError build + leanchecker OK; axioms propext, Classical.choice, Quot.sound.

## 359425 deformed monotone Hurwitz interlacing (arXiv:2308.04015, con:interlacing; authors: 1430 checks, g<=5, n<=5)
- scripts/hurwitz.py: cut-and-join recursion, exact rationals; Narayana identity check passes; real-rootedness by exact Sturm count; interlacing by 60-digit roots.
- No failure: g=0 n<=7 |mu|<=13; g=0 n<=2 |mu|<=20; g=1 n<=7 |mu|<=11. PARKED.

## 359278 set reconstruction (n >= k^2+2k)
- k=3: non-injective n=8,9,10 (69, 6, 2 pairs); injective n=11..14. k=4: injective at n=13. Domain k=3, n>=15 not reached. PARKED.

## Hook strengthening for 359279 (ordinary proof; outputs/359279-proof.md section 4)
- Hook weight formula verified on 420 random cases (scripts/hookcheck.py).
- First hook collisions: c=n-k=4 at n=12 (k=8); c=5 at n=16 (k=11, verified exactly); c=6 none up to n=26.
