# Mathematical checkpoint: relative Tor is the unpaid operation

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

Full C remains unchanged. Initial exact Tate runs: 25 quotient examples,
p=0,...,4 and their entire possible internal ranges, plus 63 regular
instances in three fixed-module quadratic pencils, p=0,...,5. No
counterexample found. These are not an isomorphism census or a theorem.

1. Polynomial transfer fails to descend directly. In C[x,y], set
f1=x^2-xy, f2=y^2, t1=x,t2=y, Delta=C. These satisfy the actual
commuting-form/ordered-basis/triangular identities, with C12=x. The
sequence is regular: x^2-xy and y^2 are relatively prime. In R=S/(f1,f2),
t1^2=xy !=0. Thus N/(f1,f2) is not a module over T/(y1^2,y2^2) under
the source right T action. Nonzero xy follows, for example, from the
standard basis 1,x,y,xy; the two defining quadrics have independent
leading terms x^2,y^2. The source module transfer cannot simply replace
T by its pure-power quotient. This does not refute C: the same example
admits a standard simultaneous initial degeneration and is already paid.

2. Multiplicative filtration is additional information. Over Q let Delta
be the division Hamilton quaternion algebra with i^2=j^2=-1 and ij=-ji.
In Delta[x,y], t1=x and t2=ix+jy commute and have a full left-Delta
ordered monomial basis. The leading y coefficient of t1^a t2^b is j^b,
so independence and spanning follow degreewise by triangular elimination.
They satisfy t1^2=f1, t2^2=-f2 for f1=x^2,f2=x^2+y^2. In the source
reversed-exponent order, the descending degree-one slot Delta*t2 has
right product t2*i=-i*t2-2*t1, outside that slot. Hence it is not an
algebra filtration with all Delta in degree zero. This is an abstract
characteristic-zero interface countermodel, not a counterexample over
the source's k/C field, not a universal claim about its chosen outputs,
and not a counterexample to C. The module filtration needs only left
Delta and right polynomial action; a bar/Tate transfer needs more.

3. Exact full-complex rank target. Write f_h=sum_i x_i g_hi, e.g.
g_hi=(1/a_h) partial_i f_h in characteristic zero. The Tate k-resolution
over R has underlying R tensor Lambda(e_i) tensor Gamma(u_h), with
d e_i=x_i and d u_h=sum_i g_hi e_i; e_i has bidegree (1,1) and u_h
(2,a_h). All higher homotopies on the Koszul k-resolution can be taken
zero because these odd wedge multiplications anticommute. The
Eisenbud-Peeva book Construction 4.1.3, Proposition 4.1.4 and Remark
4.1.5 pay its exactness. Tensor with M. For fixed (p,j) its term dimension
is determined by HF(M) and (a_h), therefore equals the lex model's term
dimension. C is equivalent to

 rank d_(p,j)(M;f)+rank d_(p+1,j)(M;f)
 >= rank d_(p,j)(N;powers)+rank d_(p+1,j)(N;powers).

The source compares the Koszul subcomplex with zero Gamma exponent.
It does not compare all the additional g_hi maps or their adjacent rank
sums. A proof via compatible filtered higher homotopies or an actual
algebra/module-pair degeneration would pay the missing transfer; neither
is supplied. A generic Shamash rank upper bound on beta_R(M) using
beta_S(M) does not give a lower bound on beta_A(N), whose Shamash complex
may cancel.
