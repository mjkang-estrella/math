# Full relative complete-intersection comparison C: focused second attempt

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0; original code MIT. Third-party materials are
private reading inputs and retain their original rights.

**UNRESOLVED.** Full C is neither proved nor refuted. No smaller theorem is
nominated, no independent proof or contribution verdict is claimed, and the
accepted campaign count remains **4/10**. This report records an attempted
filtered-complex bridge, its exact remaining requirements, and an all-degree
example showing how changing the base changes relative Tor while leaving the
ambient quotient and ambient resolution unchanged. The example satisfies C;
it is not a counterexample to the target.

## Frozen full target

For every characteristic-zero field k, n>=1, and sequence
2<=a_1<=...<=a_n, let S=k[x_1,...,x_n]. Let f_1,...,f_n be any homogeneous
regular sequence with deg f_h=a_h, and let I be any proper homogeneous ideal
containing F=(f_1,...,f_n). Set

    R=S/F, M=S/I, P=(x_1^{a_1},...,x_n^{a_n}), A=S/P.

In each degree d, let J contain P_d and the lexicographically greatest
(dim I_d-dim P_d) monomials outside P_d, for x_1>...>x_n. The stipulated
source supplies existence, ideal closure, and HF(S/J)=HF(M). Put N=S/J.
The target remains

    beta^R_(p,j)(M) <= beta^A_(p,j)(N)
    for every p>=0 and every integer j.

All fields, sizes, degree lists, regular sequences, additional generators,
and homological/internal degrees are retained. Infinite relative resolutions
are the object. No split, quadratic, generic, low-dimensional, bounded-p,
fixed-base or simultaneous-initial-pair restriction replaces the target.
`original-scope.md` preserves the complete original statement verbatim.

## Authentication and mandatory continuity

Before relying on retained source copies or code, the complete original r10
inventory authenticated against the externally supplied seal

    ab76359004bde5f7615f04fc4d7893c4ede636cc5be22238b7521ca565fd679c.

All 61 inputs, 26 outputs, and the four manifest/seal metadata files match:
exactly 91 files, with no extra member. All 25 retained OpenAI Git blobs were
also recomputed and matched to the complete `sources/preprints-tree.json`.
The pinned revision is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
Theorems at that revision are accepted as instructed; upstream truth was
not audited. No r10 checker, verifier or imported local module was executed.

The complete structural discovery brief at
`elementary-unimodality-parent/fresh-r10-brief.txt` was read, lines 1--1772:
119315 Unicode characters, 119730 UTF-8 bytes. Its SHA256 is
`97f5b23fcd79fa6abc3850e6efdd3e001530665e26e9811fc5a4e61dcef9fb57`.
Earlier findings, corrected diagnostics and scope/contribution vetoes are
retained. Read in full: r10 scope, candidate, source contracts and literature
screen, plus parent r10 disposition and verification. Historical directory
permissions and broad discovery instructions are superseded only as the
current assignment directs. U, H, B, T2, EPnI, poly-Zp, FK F/G and the crossing
manuscript are not reopened. No result is relabelled or split for counting.

`input-snapshot-before.json` binds the complete external r10 tree and the
specific context/continuity files consulted outside it. New primary-source
copies are private in this directory. `source-contracts.json` distinguishes
new semantic reading from earlier r10 readings and mere lexical searches.
No full continuity package has been recopied.

## Actual source interfaces and the new route attempted

The pinned `thm:main` and `cor:characteristic-zero` compare ambient S-Betti
numbers. `thm:forms` and `mono:transfer` give a field extension K/C, a finite
central division algebra Delta over K, commuting forms t_h, a full ordered
left-Delta basis t^alpha of E=Delta[x], and an exact polynomial-module
transfer. Write T=K[y_1,...,y_n] for the right action through t_h and
m=dim_K Delta. `filt:comparison` and `mono:bound` apply to right T-modules.
They do not assert an R-to-A relative Tor transfer.

There is nevertheless useful additional compatibility to investigate. Let
B denote the **commutative source subalgebra** containing x_i and t_i;
this B is not the target pure-power quotient A. If c belongs to B, expand
c=sum_alpha c_alpha t^alpha in the full left-Delta basis. Because c commutes
with each t_i, for every b in Delta and exponent beta one has

    (b t^beta)c = sum_alpha b c_alpha t^(alpha+beta).       (1)

Every sum is finite and the multiplication order of coefficients is as
written. Thus right multiplication by c is an operator respecting the
additive exponent filtration, with the appropriate shift given by the
least exponent in c. Products c,d in B have the reversed coefficient
convolution d_beta*c_alpha in an expansion obtained by moving c past
coefficients; this does not require Delta to be commutative. At the unique
least exponent, the product of the two nonzero leading coefficients is
nonzero because Delta is a division algebra. This pays compatibility for
the centralizer B and its action on E. It does not pay compatibility for
all right multiplications by Delta.

Apply `mono:bound` to F and I with the **same** division forms and order.
For F alone the leading right T-submodule must be Delta tensor P: its
monomial exponent ideal contains P and its quotient has the complete-
intersection Hilbert function of A, so inclusion and equal dimensions force
equality in every degree. For I it is Delta tensor K_0 for a monomial ideal
K_0 containing P. Consequently the source yields the compatible module
pictures

    gr(E/FE) = (T/P)^m,
    gr(E/IE) = (T/K_0)^m.                                (2)

Their Hilbert functions match the original modules, with factor m. Equation
(2) is a promising starting point for a complex comparison; it is still a
statement about modules. The first quotient in (2) has not been identified
as a specialization of a filtered base algebra acting freely in the
required way on every resolution term.

I tried to lift a resolution or the whole Tate complex through this module
picture. A free R-resolution, tensored with Delta after coefficient field
extension, has copies of E/FE as its terms. To lift a minimal resolution
over T/P, one would need covers and lifted syzygy maps whose leading maps
are T/P-linear and whose associated graded complex is exact. Arbitrary
leading relations in IE can involve left division coefficients. A lift w
of a leading monomial need not be central or in B. Right multiplication by
w is left-Delta-linear but need not commute with t_i; left multiplication
by w commutes with the right T-action but need not have the required
Delta/filtration compatibility on coefficient positions. Equation (1)
does not cover that w. No all-kernel lifting/strictness theorem was proved.

The direction of comparison matters: merely making the associated graded
of an original minimal R-resolution exact would give a resolution on the
special side with the **original** ranks, and hence an inequality in the
opposite direction. The desired degeneration argument instead lifts a
minimal special-side resolution to a possibly nonminimal original-side
resolution, or directly compares homology of filtered complexes. The
source module picture has not supplied that lifting operation.

One can also compare the transferred free Koszul resolution of the residue
coefficient space with m copies of the T-Koszul resolution, by uniqueness
of minimal polynomial-ring resolutions. Such a comparison is T-linear;
no compatibility with the original left S-action, preservation of every
IE, or compatibility with the regular-sequence homotopies follows merely
from that uniqueness. Descending this free polynomial-level comparison
therefore leaves an additional unproved operation. No assertion that
every possible compatible choice is impossible is made.

## A genuinely variable relative differential with fixed ambient data

Here is an exact diagnostic over Q, hence also over C. It is standard
Tate/matrix-factorization arithmetic, not a frontier nomination. Put

    S=Q[x,y], I=(x^2,y^3), M=S/I, a=(3,4),
    F0=(x^3,y^4),       R0=S/F0,
    F1=(x^3+y^3,y^4),   R1=S/F1.

Both bases are regular. For F1, x^3+y^3 is not divisible by y, so y^4 is
a nonzerodivisor modulo it; the corresponding assertion for F0 is
immediate. Both sequences lie in I. The quotient M has monomial basis
1,x,y,xy,y^2,xy^2 and Hilbert function (1,2,2,1). Its ambient minimal
resolution is the same Koszul resolution on x^2,y^3 in both cases, with
series

    P_M^S(t,z)=(1+t z^2)(1+t z^3).

For clarity, P_M^R(t,z)=sum beta^R_(p,j)(M) t^p z^j. The full relative
series are

    P_M^R0 = (1+t z^2)(1+t z^3)
              / ((1-t^2 z^3)(1-t^2 z^4)),                (3)
    P_M^R1 = (1+t z^2)/(1-t^2 z^4).                       (4)

Here is an all-degree proof, independent of finite extrapolation. Use
Tate generators e_x,e_y of bidegree (1,1), u of (2,3), v of (2,4).
For F0 choose d u=x^2 e_x and d v=y^3 e_y. These even differentials vanish
on M. The remaining Koszul complex splits over Q into the x and y factors.
For Q[x]/x^2, its x-Koszul homology is one copy of Q at (0,0) and one at
(1,2); for Q[y]/y^3 the y-Koszul homology occurs at (0,0) and (1,3).
Tensor with the zero-differential divided powers u,v to obtain (3).

For F1 choose d u=x^2 e_x+y^2 e_y and d v=y^3 e_y. On M this is

    d e_x=x, d e_y=y, d u=y^2 e_y, d v=0.

The complex now splits into the x-Koszul complex, the one-variable Tate
complex for Q[y]/y^3 on e_y,u, and the zero-differential divided powers v.
The middle complex is exact except for Q in degree zero: its maps
alternate y and y^2, with ker(y)=image(y^2) and ker(y^2)=image(y).
Tensoring these complexes over a field gives (4), with no convergence
problem in a fixed bidegree. This also follows from the exact zero-divisor
pair x^2,xy in R1: in Q[x,y]/(x^3+y^3), both are nonzerodivisors and
 y^4=-x^2*xy. Reduction modulo their product gives kernels equal to the
opposite principal images. Multiplication by x^2 and xy, both degree two,
is a rank-one minimal periodic R1-resolution of M. Its shifts are j=2p,
which agrees with (4).

For example beta^R0_(1,3)(M)=1 whereas beta^R1_(1,3)(M)=0. Thus the same
Hilbert function, the identical ambient module, and the identical ambient
minimal resolution do not determine the relative answer. The extra data
are visible already on Koszul homology: the degree-(1,3) class represented
by y^2 e_y is zero as an image of d u for F0 and nonzero as that image for
F1. The second differential removes its whole divided-power tower, with
the compatible exterior-class tower. This is an actual all-degree
cancellation mechanism, not an inference from ambient dimensions.

The common lex-plus-powers ideal is

    J=(x^2,xy^2,y^4),  A=Q[x,y]/(x^3,y^4),  N=S/J.

For each degree its surviving box monomials are the lexicographically
smallest required number, giving HF (1,2,2,1); ideal closure is immediate
from the displayed generators. This diagnostic does not violate C. R0=A,
so Murai--Peeva already bounds (3) by beta^A(N) in all degrees. Moreover
(3) equals (4) times (1+t z^3)/(1-t^2 z^3), a series with nonnegative
coefficients and constant term 1. Thus (4) is bounded as well. No restricted
instance of C is being offered as the task's solution. The point is to
identify precisely what a comparison must transport: the cycles and their
homotopy actions, not just the ambient ranks.

## Full remaining comparison, with all degrees retained

For an arbitrary input of C choose f_h=sum_i x_i g_hi, for example the
Euler choice g_hi=(partial_i f_h)/a_h. The Tate complex computing relative
Tor has term

    T_p(M;f)=M tensor Lambda(e_1,...,e_n)
                  tensor Gamma(u_1,...,u_n),
    d e_i=x_i, d u_h=sum_i g_hi e_i,
    deg(e_i)=(1,1), deg(u_h)=(2,a_h).

The wedge homotopies have anticommutator f_h with the Koszul differential,
square to zero, and anticommute with each other; the standard Shamash/Tate
exactness theorem applies to the regular sequence. These are credited
classical operations. In bidegree (p,j) its dimension is

    c_(p,j)=sum_(|sigma|+2|b|=p)
             HF_M(j-|sigma|-sum_h a_h b_h).

The matching Hilbert function makes c_(p,j) identical for N over A. Write
r_(p,j) for rank of d:T_(p,j)->T_(p-1,j), with r_(0,j)=0. Then full C is
exactly

    r_(p,j)(M;f)+r_(p+1,j)(M;f)
       >= r_(p,j)(N;powers)+r_(p+1,j)(N;powers)             (5)

for every original input and every p,j. The difference of the two sides
is the reversed difference of the homology dimensions, after subtracting
from c_(p,j). No sign or minimality assumption is inserted in (5).

A concrete sufficient bridge, still **unproved**, is this: for each input,
produce K_0 containing P as in (2), a positive factor m after field
extension, and finite filtrations of every internal-degree strand of
T(M;f)^m, such that the associated graded complex is isomorphic, preserving
homological and internal degrees, to T(S/K_0;powers)^m. Filtration-preserving
maps have rank at least their associated graded ranks. Applying this to
both adjacent maps proves the comparison to S/K_0, and Murai--Peeva then
compares S/K_0 with N. An equivalent sufficient implementation would use
complexes flat over a parameter whose generic fibers are the original
complex after field extension and whose special fibers are the target
complex; merely connecting two arbitrary special points in a family is
insufficient. This is a required construction, not a hypothesis silently
assumed in a claimed proof.

At fixed j all strands are finite: a_h>=2 implies p<=j whenever a term is
nonzero. Thus such a bridge need not invoke an unjustified convergence of
an infinite filtration. It must still exist for every j without a bound,
and must handle all g_hi interactions with the Koszul differential and
all divided-power positions. The source's ambient Koszul comparison and
(2) do not identify those full associated graded maps. Example (3)--(4)
shows that their Koszul-homology actions already contain additional real
information. Comparing that first action alone would still not automatically
control all later homology or spectral-sequence interactions.

No such construction or proof of (5), and no counterexample to (5), was
obtained. Field extension/descent does not fix this gap: each fixed Tate
matrix has rank unchanged under field extension, so a complete complex-
field proof could descend through the finite coefficient field. The
unpaid operation is the arbitrary-base comparison itself.

## Inherited objections, unchanged

1. For R=C[x,y]/(x^2-xy,y^2), t=(x,y), one has t_1^2=xy!=0. The right
   polynomial action does not factor through the pure-power quotient.
   This rejects the indicated shortcut, not C or every possible construction.
2. For Hamilton quaternions over Q, t_1=x, t_2=ix+jy satisfy
   t_2 i=-i t_2-2t_1. A left-division/right-polynomial module basis does
   not automatically give an algebra filtration. This is over Q and is
   not a counterexample to every complex source output. Equation (1)
   only concerns the actual commuting subalgebra and does not erase this.
3. Simultaneous initial-pair degeneration with in(F)=P is already
   Murai--Peeva Lemma 4.6.2 / Gasharov--Horwitz--Peeva Proposition 2.6.
   The full relative pure-power comparison is already MP Theorem 4.6.5.
   Neither conditional route is nominated here.
4. Ambient b=0 Koszul rows do not control the entire divided-power
   differential. Hilbert-function matching gives terms, not (5).
5. Nonminimal Shamash ranks cannot replace beta^A(N). Already M=R,N=A
   have relative series 1 despite positive higher terms in the unminimized
   ambient-Shamash bound. The present example concerns actual homology,
   not that unminimized bound.
6. Earlier 25 examples through p=4, 63 regular pencil cases through p=5,
   and two bar checks through p=2 overlap. They are carried as r10 history,
   not rerun, summed, promoted to independent cases, or extrapolated.
   The corrected negative-control failure in r10 remains recorded.

## Primary antecedents, novelty limits, and exact diagnostics

Murai--Peeva's retained text was re-read at Lemma 4.6.2 and Theorem 4.6.5,
including the proof. The underlying Gasharov--Horwitz--Peeva Proposition 2.6
was now retrieved directly and read with its full homogenization/free-
resolution proof. The base ideal and the containing ideal are homogenized
simultaneously, with parameter and parameter-minus-one regular on both
quotients. This is precisely why their operation controls relative Betti
numbers; a module-only replacement is not the same operation.

Eisenbud--Peeva Definition 3.4.1, Proposition 3.4.2 and Construction 4.1.3 /
Proposition 4.1.4 / Remark 4.1.5 were re-read. They supply existence of
higher homotopies and Shamash/Tate exactness. They do not supply the
comparison-compatible system or its specialization required here.

Caviglia--Kummini's *Poset embeddings of Hilbert functions and Betti numbers*
was additionally read at its actual Theorems 3.1 and 4.1 interfaces. Their
A and B denote **ambient polynomial rings** presenting R and its extension.
Theorem 3.1 propagates their ambient inequalities to R[z]/(z^t); Theorem
4.1 is the Artinian reduction of ambient LPP. It does not state the
arbitrary complete-intersection relative transfer. The distinction appears
explicitly before Theorem 3.1. Its full long proof was not audited here;
the stated interface suffices to exclude treating it as the missing C.

The earlier Mermin--Murai ambient results, Caviglia--Sammartano fixed-
Hilbert-polynomial results and I226 ambient-cancellation work remain as
screened in r10; they were not independently re-audited in this round.
No exact full-C theorem was located in this bounded primary screen. This
is not a worldwide novelty guarantee or a claim that C is a newly
identified named open problem. The diagnostic series and operator
bookkeeping above are standard technical work, not a substantial result.

`diagnostics.py` is a new standalone exact implementation. It imports no
r10 code. Quotients have explicit monomial reduction rules; elimination
uses rational fractions. It constructs full bidegree Tate matrices for the
two choices of base and the common LPP quotient, verifies 360 internal-
component compositions, and computes every possible internal degree through
p=6 (including incoming maps from p=7). It verifies (3)--(4) against their
series coefficients, checks the same original C inequalities in that finite
range, tests free modules and the residue field, and confirms the rank-six
opposite annihilator images in the 12-dimensional R1. Normalized bar
homology independently agrees through p=1 for all three pairs, using
separate resolution machinery but the same monomial quotient arithmetic.
These are not independent arithmetic implementation or independent review.
There is one fixed ambient quotient with two base choices, plus its LPP
comparison, not a new census or an enlarged historical independent count.

The initial run reached the negative-control assertion and failed because
that assertion incorrectly expected the full differential to have rank
zero when the even map was omitted; its Koszul part need not vanish.
The correction compares rank(actual)=rank(omitted-even)+1. The exact initial
code, pre-execution hash, empty stdout and failure stderr are retained.
The final pre-execution record and successful receipt are separate. Nothing
mathematical rests on the failed assertion. The successful data digest is
`f77cc0c0c130cfdd2988b22a1c85a57d1f7952b63a82d39d1c7515b0171507eb`.

The all-degree proofs of (3)--(4) above do not follow by extrapolating that
finite receipt. Neither the proofs nor the finite computations solve C.
No Lean or manuscript package was implemented. A future formalization of
C would have to include its actual new comparison construction, the Tate
exactness dependencies and all-degree rank comparison; formalizing only
these finite matrices would not be a formalization of C.

## Integrity and disposition

The manifests bind exact membership, file sizes and SHA256 bytes. The seal
binds both manifests; its detached SHA256 is supplied externally in the
handoff. The verifier authenticates own and external inventories and all
25 pinned blobs before executing only the new diagnostic under a write-
and network-denying audit hook, isolated Python and disabled bytecode.
It compares stdout to the frozen receipt and regenerates nothing. Before/
after whole inventories cover this package and the external inputs on
success and failure. Wrong-anchor, payload-corruption and authenticated
checker-failure rejection tests use temporary copies only within this
owned directory, then remove those copies. The first integrity-control baseline uncovered a detached-seal text-format
mismatch (r10 uses a sha256sum filename line, this round a bare digest).
The parser was corrected to accept exactly those two formats; initial
verifier bytes, authentication record and failure are retained.
Hash commitments establish
integrity under a trusted external anchor, not mathematical truth or
independent contribution acceptance. External r10 references are required;
standalone portability is not claimed.

All writes are within `relative-ci-r2/`. No nested agents, shared ledgers,
other candidates/reviews/source trees, staging, commits, publication,
uploads or submissions were used. No count change is requested. Parent
integration and independent gates remain separate. **Full C is retained
UNRESOLVED with the arbitrary-base filtered Tate comparison unpaid.**
