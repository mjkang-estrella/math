# MathDB 338822: genuine source question, but no strict discovery credit

**Decision: credit 0.** The literal quadratic-harmonic/Seiffert conjecture is
false, and a closed Lean counterexample is provided. However, the failure is
an immediate corollary of an established theorem. It does not qualify under
the user's requirement for substantive new mathematical discoveries.

## Exact source

Meštrović–Andjić, *Two Curious Inequalities Involving Different Means of Two
Arguments*, Resonance 28(12) (2023), Conjecture 1.2, p. 1893, states Q+H≤2P
for every positive x,y. The actual publisher page was visually inspected;
the PDF hash equals the already-frozen publisher source from the separate
accepted exponent-classification outcome. The arXiv version labels this
Conjecture 1.3. A fresh complete MathDB 338822 snapshot remains open with
empty solution/comment/progress fields. These facts do not certify novelty.

## Decisive prior theorem

Jiang–Qi, *Some sharp inequalities involving Seiffert and other means and
their concise proofs*, Math. Inequal. Appl. **15**(4) (2012), 1007–1017,
DOI 10.7153/mia-15-86, Theorem 5.3 (p. 1015), proves in particular

    P(x,y) < (2 A(x,y) + G(x,y))/3,  x≠y>0.

Remark 5.1 (p. 1016) explicitly credits this special inequality to an older
2003 paper. The 2012 actual publisher PDF and proof were read; the 2003
full body is not claimed read. Primary URL:
https://files.ele-math.com/articles/mia-15-86.pdf .

At x=19999,y=1, one has A=10000, G=sqrt(19999)<142,
Q=sqrt(199980001)≥14000, and H>0. Consequently the prior theorem gives

    2P < 2(20000+142)/3 = 13428 < 14000 ≤ Q < Q+H.

Thus a pre-existing general theorem immediately supplies the proposed
negative answer at the very witness used below. An unposted observation
about a still-open database entry is insufficient for strict discovery credit.
This is also separate from the accepted real-exponent classification at
MathDB 338823; no additional credit is taken from their shared source paper.

## Independent elementary Lean certificate

`formal/SeiffertCounterexample.lean` uses literal H, Q and genuine Real.arcsin
in P and proves the positive-input counterexample (19999,1). It bounds
cos(1/20) using Mathlib's standard Taylor error estimate, deduces
asin(9999/10000)>29/20 from pi>3, and obtains 2P<400000/29<14000≤Q+H.
This alternate formal proof does not make the mathematical result new.

## Further lead, expressly unproved

The ratio R(z)=(z/asin(z)-1+z²)/(sqrt(1+z²)-1+z²) has expansion
R(z)=5/9+(2/135)z²+O(z⁴) near zero and endpoint limit sqrt(2)/pi.
Numerics suggest one interior maximum near z=0.4351882603 with value
0.5569776584, and one crossing of 1/2 near z=0.975908096.
No global shape theorem, uniqueness theorem, sharp parameter classification,
formal proof or novelty finding is asserted. Such a classification, if ever
pursued, would require its own source/novelty/eligibility assessment.

Vukšić (2015), *Seiffert means, asymptotic expansions and inequalities*,
Table 1 and surrounding discussion (pp. 134–138), was read in the actual
accessible PDF. It discusses necessary asymptotic parameters and excludes
combinations whose numerically tested endpoint-style inequalities fail;
it does not supply the above ratio classification in the inspected sections.
No inference of global novelty is made from that limited comparison.
