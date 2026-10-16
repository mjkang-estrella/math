# Relative complete-intersection Betti extremality: r10 unresolved

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0; original code MIT. Third-party reading copies
remain private and retain their original rights.

**Disposition: UNRESOLVED.** Full target C is neither proved nor refuted.
No substantial theorem is nominated, independently reviewed, or counted.
The campaign remains 4/10. This round does not continue U, H, B, the
crossing-number manuscript, or the interacting-barrier spectral task.

## 1. Frozen target and dependencies

For every characteristic-zero field k, every n>=1, every integer sequence
2<=a_1<=...<=a_n, every homogeneous regular sequence f_1,...,f_n in
S=k[x_1,...,x_n] with deg f_h=a_h, and every proper homogeneous ideal
I containing F=(f_1,...,f_n), put

    R=S/F, M=S/I, P=(x_1^{a_1},...,x_n^{a_n}), A=S/P.

Let J contain P and, in degree d, the lexicographically greatest
dim I_d-dim P_d monomials outside P_d, for x_1>...>x_n. Set N=S/J.
The pinned source supplies existence of these spaces, their ideal
closure, and HF(M)=HF(N). The target, frozen in original-scope.md before
sustained proof work, is

    C: beta^R_(p,j)(M) <= beta^A_(p,j)(N)
       for every p>=0 and j in Z,
    beta^R_(p,j)(M)=dim_k Tor^R_p(M,k)_j.

All full-length homogeneous complete intersections, all additional
generators, and all homological/internal degrees are retained. Resolutions
over R and A are generally infinite. No quadratic, generic, split-form,
low-dimensional or bounded-homological-degree substitute is a success.
The zero module was not part of the frozen proper-ideal scope.

The stipulated input is openai/math at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, family 200:
*The Artinian Lex-Plus-Powers Betti Theorem* and its
*Commuting Division-Coefficient Forms* companion. Actual hypotheses and
interfaces, rather than catalogue abstracts, were read. Theorems are
accepted as instructed, without auditing their upstream truth.

The source's thm:main and cor:characteristic-zero already prove the
analogous inequality with **S in both superscripts**. That ambient theorem
is not C. Its thm:forms and mono:transfer supply commuting t_h in
Delta[x], a full left-Delta ordered monomial basis, and transfer of a
minimal S-resolution to a minimal resolution over a right-acting
polynomial ring T. Its filt:comparison and mono:bound supply a monomial
M0 containing P, with matching Hilbert function and larger ambient Betti
numbers. None of those statements supplies a relative R-to-A Tor transfer.

## 2. Screening, continuity, and paid operations

The catalogue title list and complete sources/preprints-tree.json were
searched; the truncated sources/tree.json was not used. Selected catalogue
entries included 168 and 193--210. Family 200 was selected after discovering
that its stronger ambient Betti conclusion was already paid. The complete
tree's EGH/lex-plus-powers/division-coefficient path search identified its
two companion directories; all 25 retained text blobs match their pinned
Git identities. Source contracts state what was actually read, as distinct
from retrieved or lexically searched.

The full r8 and elementary-unimodality-r2 inventories authenticated to the
user-supplied seals, respectively
6db6112bf4297450c063652b5cc415d8a4f2d20b8b5138753349fcbafbfd3600 and
6acd4f102adb468822a74642de8e43374ab10628e86d74d20f3c50c663cb55aa.
Their full candidate reports were read. No prior code was executed. U and
its cyclic-root/primitive-Young/live-jump obstructions remain unresolved;
no U result is reused as a new claim. Current ledgers and R023--R026
acceptance records were consulted for scope/overlap, not as mathematical
dependencies of C.

An exact project-local family search also found I226. Its full report was
read and retained. It already pays ambient consecutive cancellations,
records a scalar one-step degeneration obstruction, and classifies its
Clifford-size argument as technical. These are excluded lanes, not r10
nominations. I226's ambient cancellation conclusion does not supply C.

The primary literature screen found the following stronger antecedents:

* Mermin--Murai (2011), Theorems 3.1/8.1 and 9.2, pay the pure-power
  **ambient** comparison and cancellations. The source already credits
  that monomial step; repeating it earns no contribution.
* Murai--Peeva (2012), Theorem 4.6.5, pays the full graded **relative**
  comparison and consecutive cancellations when the base ring is the
  pure-power quotient A. Its Lemma 4.6.2 also pays relative Tor comparison
  for a simultaneous initial degeneration of an algebra and its quotient.
  The proof of 4.6.5 uses polarization, coordinate transformations and
  prescribed-power routes. This pays the second half of a possible proof
  of C, once an arbitrary R-module has been transferred to A. It does
  not state that first half for arbitrary regular sequences.
* Caviglia--Sammartano's *Syzygies in Hilbert schemes of complete
  intersections*, Section 5, concerns expansive ideals at fixed Hilbert
  **polynomial** over Clements--Lindstrom rings. Theorem 5.3 treats
  quadratic pure-power base rings. It is not C, which fixes the entire
  Hilbert function and changes an arbitrary complete-intersection base.
* Eisenbud--Peeva, Construction 4.1.3, Proposition 4.1.4 and Remark 4.1.5,
  pay the Shamash construction and the Tate residue-field resolution.
  Existence of higher homotopies is already Proposition 3.4.2. The unpaid
  issue here is compatibility with the desired comparison, not existence.

No exact full C statement was identified in the bounded primary screen.
This is not a global novelty guarantee, or a claim that C is a newly
discovered named open problem. The uncompleted transfer is substantial
mathematical content; its desirability is not evidence that it is true.

## 3. Direct quotient transfer fails under the actual source interface

Consider S=C[x,y], f_1=x^2-xy, f_2=y^2, Delta=C and t_1=x,t_2=y.
The forms commute and their unrestricted ordered monomials are a basis.
The triangular identities are exactly

    t_1^2=f_1+x t_2,  t_2^2=f_2.

They satisfy thm:forms with c_1=c_2=1 and C_12=x; the commutative
intermediate algebra is S. The sequence is regular: y has no common
factor with x(x-y), so y^2 is a nonzerodivisor modulo x(x-y).
The two equations have leading monomials x^2,y^2 for lex x>y and their
S-polynomial reduces to zero. Hence R has basis 1,x,y,xy and xy!=0.
In R the source's right T-action satisfies

    t_1^2=xy!=0.

It therefore does not factor through T/(y_1^2,y_2^2). A transferred
polynomial-ring resolution cannot simply be relabelled a resolution
over the pure-power quotient. This is a counterexample to that shortcut
under the actual source hypotheses, not to C. Indeed this example has
a simultaneous pure-power initial degeneration and is already covered
by Murai--Peeva's standard relative operation.

Trying ordinary initial ideals at this point requires a simultaneous
degeneration of the **base ideal** and **containing ideal**, not merely
the source's initial right T-submodule. When in(F)=P and K=in(I),
Murai--Peeva Lemma 4.6.2 gives

    beta^R(M) <= beta^A(S/K) <= beta^A(N),

with full gradings, the second inequality being their Theorem 4.6.5.
This is a paid conditional route, not a new restricted theorem nominated
as C. I226 already explains why one scalar coordinate/initial-ideal
replacement cannot be presumed universally. No new universal degeneration
was obtained here.

## 4. A module filtration is not automatically an algebra filtration

Here is a separate interface diagnostic, not a source-field counterexample.
Let Delta be the Hamilton quaternion division algebra over Q, with
i^2=j^2=-1 and ij=-ji. Its norm is the sum of four rational squares,
so every nonzero quaternion is invertible. In Delta[x,y] put

    t_1=x, t_2=ix+jy.

They commute. In each degree d, the coefficient of the largest y power
in t_1^(d-b)t_2^b is j^b, a unit. Triangular elimination against
x^(d-b)y^b proves that all ordered monomials form a full left-Delta
basis. Also t_1^2=x^2 and t_2^2=-(x^2+y^2). The commutative algebra
Q[x,y,t_2] is finite over Q[x,y]. Thus these are legitimate analogues
of the basis and triangular interface over a characteristic-zero field.

In the source's reversed-exponent order, the descending degree-one
position after t_1 is Delta*t_2. But direct multiplication gives

    t_2 i = -i t_2 - 2 t_1.

The t_1 term is nonzero and earlier, so this position is not stable under
right multiplication by Delta. It cannot be a multiplicative algebra
filtration with Delta in degree zero. The source requires only left-Delta
and right-T module compatibility, which this example respects.

This countermodel is over Q, not a field containing C. It does not claim
that every actual source output fails, that no reordered or different
filtration exists, or that C is false. Its exact purpose is to rule out
deducing algebra-filtration compatibility from the displayed module-basis
properties alone. No extension of it to all source constructions is used.

## 5. The full Tate-complex operation still needed

For any original input of C, choose

    f_h=sum_i x_i g_hi, g_hi=(partial_i f_h)/a_h.

The Tate resolution of k over R has underlying free module
R tensor Lambda(e_1,...,e_n) tensor Gamma(u_1,...,u_n), where the
homological/internal bidegrees are (1,1) for e_i and (2,a_h) for u_h.
Its differential is

    d e_i=x_i, d u_h=sum_i g_hi e_i.

This is the classical Tate/Shamash construction, not a new theorem.
For clarity, on the S-Koszul resolution of k, wedge multiplication by
sum_i g_hi e_i is a homotopy for f_h: its anticommutator with the Koszul
differential is f_h. These odd wedge multiplications square to zero
and anticommute with one another. They therefore give the system with
all higher homotopies zero. The cited Shamash theorem proves exactness
after adjoining divided-power variables. All coefficients have positive
internal degree, so this k-resolution is minimal. Tensoring it with M
computes Tor^R(M,k).

Write T_(p,j)(M;f) for this finite-dimensional term. Explicitly,

    dim T_(p,j)(M;f)
     = sum_(sigma,b: |sigma|+2|b|=p)
         HF_M(j-|sigma|-sum_h a_h b_h).

For fixed p,j this sum is finite. Since M and N have equal Hilbert
functions, their corresponding Tate term dimensions are equal. Thus C
is exactly the adjacent-rank-sum assertion

    rank d_(p,j)(M;f)+rank d_(p+1,j)(M;f)
    >= rank d_(p,j)(N;powers)+rank d_(p+1,j)(N;powers)       (5.1)

for every original input and every p,j. This follows by subtracting the
two adjacent ranks from equal term dimensions. It is a reformulation,
not a proof of the required inequality.

The source's Koszul comparison sees the subcomplex with b=0. It does not
compare the g_hi multiplication maps on all the other divided-power
positions or their interactions with Koszul boundaries. Rank inequalities
on the b=0 subcomplex do not by themselves give (5.1).

A generic Shamash rank bound gives beta^R(M) bounded by the coefficients
of P^S_M(t,z)/prod_h(1-t^2 z^{a_h}), because this counts a possibly
nonminimal free resolution. Combining it with ambient LPP only supplies
the same nonminimal upper bound for N. It does not bound beta^R(M) by
the **minimal** beta^A(N). Already M=R and N=A have actual relative
series 1, whereas those Shamash term series have positive higher terms.
No cancellation comparison was supplied to repair that route.

The precise unpaid operation is an all-input transfer from R to some
A-quotient with the same Hilbert function and no smaller relative Betti
numbers, or a direct proof of (5.1). A compatible filtered Tate/higher-
homotopy construction or an algebra/module-pair degeneration would suffice.
None is proved. Nor was a counterexample to C found. The field quantifier
does not require a new mechanism: a proof over C could descend through
the finitely generated coefficient field, since each fixed Tate matrix
has unchanged rank under field extension. The geometric/algebraic
transfer itself remains unpaid for complex inputs of unbounded size.

## 6. Exact checks and their limits

tate_checks.py uses standard-library rational arithmetic. Degree-d ideal
relations are all monomial multiples of the stated homogeneous generators;
row reduction produces the quotient and multiplication tables. It constructs
the full internal-degree Tate differentials, verifies d^2=0, and calculates
homology by exact ranks. Lex quotients are built separately from the
degreewise box prescription and their ideal closure/Hilbert functions
are checked. Regularity of each tested base is certified by its finite
quotient in n variables generated by n positive-degree forms; its Hilbert
function is additionally checked against the complete-intersection product.

The first receipt covers **25 quotient examples**, four base families,
n=2 or 3, degree lists (2,3), (2,2,2), (3,3), all p=0,...,4 and every
possible internal degree for those p. It checks 2,080 consecutive
differential compositions across the two sides. Examples include
(x^2+yz,y^2+xz,z^2+xy) with several linear and quadratic quotient ideals.
Free modules and residue fields give additional exact controls. Omitting
the even generators and using wrong wedge signs are detected. No C
violation occurs. Data digest:
96747f8ba2c458632389e1a9107d0f4d19a75ae13cf28c2059860cb47b244806.

relative_probe.py inspects three fixed monomial quotient ideals containing
x^2,y^2,z^2 and at least xy. For each it tests the 27 tuples
(a,b,c) in {-1,0,1}^3 with base forms

    x^2+a xy, y^2+b xy, z^2+c xy.

Six tuples per ideal are nonregular and excluded; **63 regular cases**
remain. All p=0,...,5 and their full possible internal ranges are checked.
No violation occurs. Within each of these three pencils all retained
relative tables agree; no variation of relative Tor at fixed ambient
module is claimed. These cases overlap some first-receipt examples and
are not 88 distinct isomorphism classes or an exhaustive CI census.

operations_checks.py verifies the two shortcut diagnostics and, independently
of the Tate differential formula, computes normalized bar homology for two
quotients through p=2. Its terms are M tensor (R_+)^(tensor p), with
differential given by adjacent multiplication and alternating signs.
The bar and Tate tables agree exactly in their entire internal ranges
for p<=2. They share the quotient arithmetic library, so this is independent
resolution machinery, not independent arithmetic implementation or review.
The first operations run failed because its missing-term negative control
compared to the wrong sign; the assertion was corrected before the successful
run. Original failure and pre-execution hashes are retained. No mathematical
claim rests on the failed run.

All three programs authenticate their local code dependencies before loading
them. Initial execution hashes were recorded before execution; final replay
authenticates all code and receipts under the detached seal. Computations
are finite supporting evidence only: no asymptotic conclusion, all-p proof,
independent proof PASS, or contribution PASS is claimed.

## 7. Integrity and disposition

Source-contracts.md and source-readings.json give actual read extents,
theorem labels, immutable URLs, Git blobs and SHA256/size records. The
input/output manifests bind exact file membership; seal.json binds their
bytes and seal.sha256 is the detached anchor to pin externally. verify.py
checks the supplied anchor, inventories, 25 pinned source blobs, copied
continuity evidence and both complete original frozen inventories before
executing only the three authored checkers. The checker subprocesses use
isolated Python, disabled bytecode and a write/network-denying audit hook.
Stdout must match retained receipts. It regenerates nothing. Whole-tree
hashes before and after cover r10, r8 and U-r2, including on checker failure.
Hashes establish integrity under a trusted anchor, not mathematical truth
or independent review. The verifier requires the frozen sibling continuity
packages; no standalone portability is claimed.

The completed material is technical diagnostic work. It does not solve C
by replacing it with a collection of lemmas, pure-power cases, finite checks,
or a conditional statement. No manuscript or Lean package was prepared.
No nested agents, shared-index/sibling edits, staging, commits, uploads,
submissions, external messages or count changes occurred. All writes were
within the assigned r10 directory. Parent integrates; full C remains
UNRESOLVED.
