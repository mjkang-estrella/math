# Candidate refutation of MathDB 352038

Status: proved mathematical/formal candidate, zero accepted credit. Independent fidelity, novelty/significance and root acceptance remain separate.

Primary target: Lachmann–Wiart, arXiv:2109.11222v1 (2021), Appendix A, Conjecture A.5, manuscript page28. The exact MathDB record and primary statement both concern the n-th largest **distinct** coefficient in the purely periodic expansion of a quadratic integer. The source page was visually inspected. No multiplicity interpretation or domain correction is used.

Put s = sqrt(3049), delta = (55+s)/2. Then 55<s<56, delta^2-55delta-6=0, and delta is irrational since 3049 is not a square. This monic integer equation proves delta is an algebraic integer of degree2. Its conjugate (55-s)/2 is in (-1,0), consistent with the reduced/purely-periodic condition; the expansion is proved directly below rather than inferred from the classical criterion.

The following is the exact repeating block, beginning with a_0:

```
55,9,5,2,2,3,3,1,1,1,6,3,1,3,1,5,2,1,8,1,1,13,3,1,1,1,1,4,1,10,4,1,1,27,18,2,1,2,2,1,1,7,3,3,7,1,1,2,2,1,2,18,27,1,1,4,10,1,4,1,1,1,1,3,13,1,1,8,1,2,5,1,3,1,3,6,1,1,1,3,3,2,2,5,9
```

For a completely reproducible exact verification, start (m_0,d_0)=(55,2) and set

m_(i+1)=a_i d_i-m_i,  d_(i+1)=(3049-m_(i+1)^2)/d_i.

The integers m_i,d_i are provided explicitly as functions M,D on Fin85 in Candidate.lean. For each cyclic index i, the kernel checks all five properties:

1. d_i>0;
2. a_i d_i <= m_i+55;
3. m_i+56 <= (a_i+1)d_i;
4. m_(i+1)=a_i d_i-m_i;
5. d_i d_(i+1)=3049-m_(i+1)^2.

The indices are cyclic, so this includes the final return to (55,2). Let q_i=(m_i+s)/d_i. Properties1-3 and 55<s<56 prove a_i<q_i<a_i+1, hence floor(q_i)=a_i and q_i-a_i is strictly positive. Properties4-5 and s^2=3049 give

q_(i+1)(q_i-a_i)=1.

Indeed the numerator product is (m_(i+1)+s)(s-m_(i+1))=3049-m_(i+1)^2. Thus q_(i+1)=1/(q_i-a_i). Since q_0=delta, induction proves that for **every** natural n the actual mathlib `GenContFract.IntFractPair.stream delta n` is present and has integer part a_(n mod85) and fractional part q_(n mod85)-a_(n mod85). This supplies the unbounded semantic bridge from the finite integer certificate to the real infinite continued fraction, including nontermination and pure periodicity.

The distinct coefficient set is

{55,27,18,13,10,9,8,7,6,5,4,3,2,1}.

Exactly six values exceed8, and8 occurs, so w_7=8. The conjectured inequality would give8<=55/7, contradicted by56>55. This refutes the universal assertion, including the source's genuine quadratic-integer domain. It does not merely find a misleading rotation, a repeated coefficient or a rational finite continued fraction.

`SourceConjecture` uses the actual mathlib stream to bind a coefficient sequence, asserts an integer quadratic equation plus integrality/irrationality, and requires a positive period starting at index0. The coefficient set is the finite image of one full period and rank is one plus the count of strictly greater distinct values. Every ordinary purely periodic quadratic integer has this encoding; repeated copies of a period give the same set. `source_refutation : ¬ SourceConjecture` instantiates these exact hypotheses. No table-validity surrogate is the final endpoint.

Classical complete-quotient arithmetic is a proof tool, not the purported discovery. The source's proved A.3/4.4 norm bound controls an individual noninitial coefficient by about s/2; our maximum noninitial coefficient27 obeys it. That bound does not imply the false all-ranks assertion. Literature novelty and mathematical significance nevertheless require independent adjudication; no worldwide priority claim is made.
