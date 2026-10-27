# MathDB367973: direct elementary finite-field product corollary, credit0

Actual Kalinin arXiv2504.07978, Conjecture2 printedp8, read in text and rendered
page. This concerns the polynomial product itself; its initial displayed degree
(p-1)^2 is inaccurate for split primes. The product, not that typo, is used.
No separate transcription-correction credit. Both conjectured product patterns
and the requested closed coefficients follow directly from standard finite-field
root products, so this lane does not propose a discovery packet.

For p=3mod4, F_p[i]=F_(p²). The root set is the field with the two coordinate
axes removed. The polynomial of the entire field is X^(p²)-X. The monic
polynomial of the axes (zero counted once) is
X*(X^(p-1)-1)*(X^(p-1)+1). Therefore

 g_p(X)=(X^(p²-1)-1)/(X^(2(p-1))-1)
       =sum_(j=0)^((p-1)/2) X^(2j(p-1)).

For p=1mod4 choose r∈F_p with r²=-1. Under evaluation i=r, each nonzero root
s occurs p-3 times: among choices m∈F_p exclude m=0, s/r and s/(2r), then
n=s-rm is nonzero and n-rm is nonzero, precisely the unit condition.
Evaluation i=-r gives the same result. Since the two evaluation maps jointly
identify F_p[i] with F_p×F_p, this proves

 g_p(X)=(X^(p-1)-1)^(p-3)
       =sum_(j=0)^(p-3) binom(j+2,2) X^(j(p-1)) modulo p.

The coefficient identity uses
(-1)^j binom(p-3,j)=binom(j+2,2) modp; its denominators j! and2 are invertible
in the displayed range. Thus b_j=(j+1)(j+2)/2 modp is the requested formula.

The standard finite-field root theorem is also actually inspected in pinned
Mathlib FieldTheory/Finite/Basic.lean, FiniteField.roots_X_pow_card_sub_X;
this is a classical fact, not proposed new machinery. Exact Gaussian-pair
multiplication checks every coefficient for ten primes3..31, including all
four source examples; check_gaussian_polynomial.py passes.

This exclusion is for being an immediate standard corollary under the strict
campaign rule. It does NOT assert someone previously posted the exact formula.
No worldwide-priority or external Lean replay claim. Calderon2608.00347 was
also inspected, but its explicit resolution is the DIFFERENT Conjecture3
inert-prime rectangular binomial congruence, not this coefficient question;
it is not used as evidence that Conjecture2 was previously solved.
