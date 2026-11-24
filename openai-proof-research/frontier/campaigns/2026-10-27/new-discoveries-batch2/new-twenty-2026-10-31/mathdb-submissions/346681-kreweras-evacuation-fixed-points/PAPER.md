# The two Kreweras evacuation products

Complete Lean formalization, stage 6, 20 November 2026. MathDB 346681.

We prove both formulas in Hopkins–Rubey, Conjecture 6.3, for the literal
finite Kreweras words and the source's evacuation and dual evacuation.
The proof passes through domino chains and a three-sector slit-plane
unfolding. The final enumeration is established by constructing an
algebraic coefficient array and verifying the exact finite-walk recurrence.
This avoids importing a canonical-factorization theorem, a walk-count
formula, or a path decomposition as an assumption. The endpoint is
Kreweras.mathdb346681. Its printed transitive axioms are exactly propext,
Classical.choice and Quot.sound.

## Literal source definitions beside the Lean definitions

The source is Hopkins–Rubey, *Promotion of Kreweras words*, arXiv:2005.14031v4 (2021), Selecta Mathematica 28 (2022), article 10, DOI 10.1007/s00029-021-00714-6. We use the cached text extraction of the reviewed source; no new web or prior-art search is claimed in this implementation stage.

The source's definition of Kreweras words, verbatim from its introduction, is quoted below. The other excerpts are verbatim from its Section 2 as extracted from the PDF. PDF extraction preserves line wrapping and may separate a displayed formula from its surrounding prose.

```text
Kreweras words are words consisting of n A’s, n B’s, and n C’s in
which every prefix has at least as many A’s as B’s and at least as many A’s as C’s.
```

```text
   Let P be a poset with ℓ elements. For us, a linear extension of P will be a list
(p1 , p2 , . . . , pℓ ) of all of the elements of P , each appearing once, for which pi ≤ pj
implies that i ≤ j. We use L(P ) denote the set of linear extensions of P .
   For each 1 ≤ i ≤ ℓ − 1, we define the involution τi : L(P ) → L(P ) by
                                 
                                 (p , . . . , p , p , p , p , . . . , p ) if pi and pi+1 are
                                    1           i−1 i+1 i i+2           ℓ
        τi (p1 , . . . , pℓ ) :=                                           incomparable;
                                 (p , . . . , p )                         otherwise.
                             1       ℓ

In other words, τi swaps the ith and (i+ 1)st entries of a linear extension, if possible.
6                            SAM HOPKINS AND MARTIN RUBEY


                                   Bn                   Cn

                                    B3          An      C3

                                    B2          A3      C2

                                    B1          A2      C1

                                                A1

     Figure 3. The poset V (n) whose linear extensions are Kreweras words.


Proposition 2.2. “Removing the subscripts” is a bijection from linear extensions
of V (n) to Kreweras words of length 3n, and under this bijection, promotion of linear
extensions corresponds to promotion of Kreweras words as was defined in Section 1.

Definition 2.3. Evacuation, Evac : L(P ) → L(P ), is the following composition
of τi :
       Evac := (τ1 ) ◦ (τ2 ◦ τ1 ) ◦ · · · ◦ (τℓ−2 ◦ · · · ◦ τ2 ◦ τ1 ) ◦ (τℓ−1 ◦ · · · ◦ τ2 ◦ τ1 ).
   Again, there is an alternative definition of evacuation in terms of jeu de taquin.
Historically, interest in evacuation arose because of its close connection with the
Robinson-Schensted correspondence.
   There is an obvious duality between the linear extensions of P and of its dual
poset P ∗ : for L = (p1 , . . . , pℓ ) ∈ L(P ), we use L∗ to denote the linear extension
L∗ := (pℓ , pℓ−1 , . . . , p1 ) ∈ L(P ∗ ) of the dual poset.
   Dual evacuation, Evac∗ : L(P ) → L(P ), is defined by Evac∗ (L) := (Evac(L∗ ))∗ .
In some sense, dual evacuation is “just as natural” as evacuation. In terms of the
involutions τi , we have
        Evac∗ = (τℓ−1 ◦ · · · ◦ τ1 ) ◦ (τℓ−1 ◦ · · · ◦ τ2 ) ◦ · · · ◦ (τℓ−1 ◦ τℓ−2 ) ◦ (τℓ−1 )

```

The Lean counterparts are `Word n := Fin (3*n) → Fin 3` and `K n := {w // Valid w}`. `Valid` asserts n copies of every letter and both ballot inequalities at all prefix lengths 0,...,3n. `Element n := Fin 3 × Fin n` and `posetLE p q := (p.1=q.1 ∨ p.1=0) ∧ p.2≤q.2` are the product V×[n]. Zero-based occurrence labels correspond to the source's subscripts 1,...,n. An `Extension n` gives an equivalence from elements to positions, increasing on this relation. `wordExtensionEquiv`, `label_letter`, and `label_index` prove the occurrence-labeling bridge in Lean, including uniqueness. An arbitrary relabeling of equal letters is not used.

`adjacent N i` swaps the two zero-based positions i,i+1 when in range; `tau` performs that swap if the result is valid. `swap_valid_iff_incomparable`, `swap_orderValid_iff`, and `tau_bridge` prove its equivalence to the source operator. Equal-letter swaps fix the word, while the labeled occurrences are comparable and the source operator fixes the extension. `prefixSchedule N` lists 0,...,N-2, then 0,...,N-3, and so on. Because `languageRun` applies the list from left to right, this is exactly Definition 2.3, whose rightmost block acts first. `evac_bridge` proves compatibility with the independent poset operator.

`ReverseK n` is the language obtained by reversing each original word. `reverseLinear` reverses the extension and the relation. `dualEvac` literally reverses, applies prefix evacuation in ReverseK, and reverses back. `dualEvac_bridge` proves that this is the source's dual-poset construction. We do not assume a suffix-word identity to justify this definition. `evac_bijective` and `dualEvac_bijective` prove the implemented maps are permutations.

The kernel-reduced sanity counts are:

| n | all words | Evac fixed | Evac* fixed | source product P(n) |
|---|---:|---:|---:|---:|
| 1 | 2 | 0 | 2 | 2 |
| 2 | 16 | 4 | 4 | 4 |

The six integer cardinalities use plain `decide`. The two rational product evaluations use `norm_num`; `small_literal_one` and `small_literal_two` assemble the literal formulas for these two parameters. These checks validate the operator definitions, not the universal enumeration.

## Verbatim source conjecture

The following is verbatim cached journal text (Conjecture 6.3). The extraction
mangles the floor/ceiling and product glyphs; the readable displayed formula
immediately below it in the literal statement transcribes those glyphs.

```text
Conjecture 6.3 For all n ≥ 1, the number of Kreweras words of length 3n with
Evac∗ (w) = w is
                                      ,7n/28              ,9n/2:
                      37n/28 49n/2:     j=1 (3 j − 1)       j=1 (3 j − 2)
                                                                            .
                                            (n + 1)!

The number of Kreweras words of length 3n with Evac(w) = w is this same number
if n is even, and is 0 if n is odd.
```

## Source definitions and the result

Hopkins–Rubey, *Promotion of Kreweras words*, arXiv:2005.14031v4, Conjecture 6.3; final journal Selecta Mathematica 28 (2022), 10, DOI 10.1007/s00029-021-00714-6. The final open PDF at https://par.nsf.gov/servlets/purl/10353965 retains the conjecture. No numeric author-test ceiling is stated.

A Kreweras word contains n copies of each of A,B,C; every prefix has at least as many A's as B's and as C's. Its linear-extension poset P_n=V×[n] consists of chains A_1<...<A_n, B_1<...<B_n, C_1<...<C_n, and relations A_i<B_j,A_i<C_j exactly when i<=j. B_i,C_j are incomparable. Occurrences of a letter in their natural order identify the word with a linear extension. Evacuation and dual evacuation are the source's Schützenberger operations. Equivalently, let tau_i interchange positions i,i+1 of a linear extension when their elements are incomparable, fixing it otherwise; evacuation is the usual successive-prefix product of these involutions. Dual evacuation is evacuation after reversing the extension and dualizing the poset, followed by the inverse reversal.

Write E_n,E_n^* for their fixed-point counts. We prove

    E_(2m)=E_(2m)^*=4^m (3m)!/[m!(2m+1)!],                 (1)
    E_(2m+1)=0,
    E_(2m+1)^*=4^(m+1)(3m+1)!/[m!(2m+2)!].              (2)

These are exactly the source product for all n>=1, as checked algebraically at the end.

## 1. Domino chains

The following specialization of Stanley's evacuation/domino correspondence
(*Promotion and Evacuation*, Theorem 3.1, [arXiv:0806.4717](https://arxiv.org/abs/0806.4717)) is
proved here from the adjacent involutions. No published counting theorem is
assumed by Lean. Let e_N be the triangular prefix evacuation word, and let
p_N have indices N-2,N-4,... . Form c_N from descending blocks of odd
lengths 1,3,5,... . The involutions square to the identity and commute at
distance greater than one. Transposing the triangular word into descending
columns using these distant commutations and inducting by two on N gives

    e_N c_N = c_N p_N.

In the induction, cancel the outer descending/ascending block and commute
its remaining distant generator through the shorter word. The lemmas
slide, prefix_column, pair_two and conjugator_two carry out these word
identities; conjugation proves the displayed equality for arbitrary
involutions with these distant commutations. The source swaps satisfy them,
so source_domino_conjugation specializes the equality to extensions.

The disjoint product p_N fixes an extension exactly when each paired
adjacent pair is comparable. Indeed distant factors leave that pair's
endpoints unchanged; a nontrivial swap cannot be undone by the other factors.
The prefix ideals therefore add a comparable pair at each domino time.
Conversely, a two-element comparable difference has a uniquely ordered
rank-one intermediate ideal. Recovering these intermediate ideals gives an
extension, inverse to taking prefix ideals. Conjugation by c_N, a bijection,
then identifies evacuation fixed points with these domino chains. At odd
cardinality the first unpaired element is a singleton. This is the
initial-singleton convention of Stanley's Theorem 3.1; it is proved in the
source-specific chain and compression modules, not inferred from a citation.

An ideal has counts (a,b,c), where 0<=b,c<=a<=n. For chains containing only domino additions, the only possible additions are

    AA: (a,b,c)->(a+2,b,c);
    BB: (a,b,c)->(a,b+2,c), provided b+2<=a;
    CC: (a,b,c)->(a,b,c+2), provided c+2<=a;
    AB: (a,b,c)->(a+1,b+1,c), provided a=b;
    AC: (a,b,c)->(a+1,b,c+1), provided a=c.           (3)

The indicated upper bound n is also imposed when working in P_n. Within one chain the two new elements must be consecutive. A comparable cross pair A_i,B_j must have i<=j. Immediately before adding it, a=i-1,b=j-1, so the ideal inequality a>=b forces i>=j. Thus i=j and a=b. This proves the AB rule; AC is identical. A BC pair is incomparable. Hence (3) is complete.

Let D(a,b,c) count such domino chains from the empty ideal, without a terminal singleton. We may work in the infinite version of the poset: any path ending at a,b,c<=n has no earlier coordinate exceeding n, since all coordinates increase. Thus this removes no relevant finite-board condition.

For even n, the theorem gives E_n=D(n,n,n). Reversing a domino chain gives a domino chain in the dual poset, so E_n^*=E_n for even n. For odd n, the initial singleton for P_n must be A_1. The state then has a odd and b,c even. The AA,BB,CC moves preserve these parities; AB and AC cannot occur because their equality conditions would equate an odd and an even integer. It is impossible to reach (n,n,n). Thus E_n=0 for odd n.

For dual evacuation at odd n, the initial dual-poset singleton is a maximal element of P_n, either B_n or C_n. Reversing the rest of the domino chain leaves a forward chain of dominoes ending at P_n minus that chosen singleton. Consequently

    E_n^*=D(n,n-1,n)+D(n,n,n-1)=2D(n,n,n-1), n odd.     (4)

The equality is B/C symmetry. It remains to enumerate D at two endpoints.

## 2. The three parity sectors unfold into a slit plane

Starting from (0,0,0), the even-size domino states have just the following parity types:

    sector E: (a,b,c)=(2A,2B,2C),
    sector X: (a,b,c)=(2A+1,2B+1,2C),
    sector Y: (a,b,c)=(2A+1,2B,2C+1).

They are closed under (3): AA,BB,CC preserve the sector; AB switches E/X, and AC switches E/Y. The putative fourth even-size parity type cannot be reached. In every sector put x=A-B,y=A-C; precisely x,y>=0 are required by the ideal inequalities.

The same-sector AA,BB,CC moves change (x,y) by (1,1),(-1,0),(0,-1), respectively, when the destination remains in that sector's quadrant. The extra boundary moves are

    E(0,y)->X(0,y),       X(0,y)->E(0,y+1),
    E(x,0)->Y(x,0),       Y(x,0)->E(x+1,0).                (5)

Map these quadrant copies into the plane by

    E(x,y) -> (u,v)=(x,y),
    X(x,y) -> (u,v)=(-x-1,y-x),
    Y(x,y) -> (u,v)=(x-y,-y-1).                           (6)

Their images are disjoint:

    E: u,v>=0;
    X: u<=-1 and v>=u+1;
    Y: v<=-1 and u>=v+1.

Together they are precisely Z^2 minus the **strictly negative diagonal** {(j,j):j<0}. In each sector, (3) maps to the step set

    S={(1,1),(-1,0),(0,-1)}.

For X the images of AA,BB,CC are respectively (-1,0),(1,1),(0,-1); for Y they are (0,-1),(-1,0),(1,1). The four moves (5) give exactly the missing transitions between adjacent sectors. On the remaining outer boundaries a putative step lands on the forbidden negative diagonal. Therefore the domino chains correspond bijectively to S-walks starting at (0,0) which avoid that diagonal, while returns to (0,0) are allowed.

This is a path bijection, with the number d of dominoes serving as time. At fixed d the ideal can be recovered uniquely: in E, A=(d+x+y)/3; in X or Y, A=(d+x+y-1)/3, then B=A-x,C=A-y. Equivalently, lift the walk uniquely using (3),(5) from its initial state. Thus no choices or multiplicities are lost by suppressing a common increase of A,B,C.

Let L(t) count these slit-plane walks ending at (0,0), and J(t) those ending at (-1,0). The endpoint identifications are

    [t^(3m)]L=D(2m,2m,2m),
    [t^(3m+1)]J=D(2m+1,2m+1,2m).                         (7)

Indeed these are E(0,0) and X(0,0), respectively. We now compute L and J exactly.


## 3. The exact walk recurrence

Write h=u-v and r=v. The forbidden set is precisely h=0,r<0. The three
steps become (0,1),(-1,0),(1,-1) in (h,r) coordinates. Let a_d(h,r)
be the rational cardinality of actual walks of time d ending at (h+r,r).
Truncate a walk at its last step. For a permitted endpoint (u,v), its
predecessor is uniquely one of

    (u-1,v-1), (u+1,v), (u,v+1).

The three predecessor choices are distinct, and appending the specified
last endpoint is inverse to truncation. Thus endpointLastStepEquiv is an
actual finite-type equivalence, and endpointCount_succ gives

    a_0(h,r) = 1 if h=r=0, and 0 otherwise;
    a_(d+1)(h,r) = 0 if h=0,r<0;
    a_(d+1)(h,r) = a_d(h,r-1)+a_d(h+1,r)+a_d(h-1,r+1)
                  otherwise.                            (R)

At time zero every walk is the unique zero-position function. At forbidden
endpoints the walk subtype is empty. These prove the initial and boundary
conditions directly. Induction on d proves uniqueness of any rational array
satisfying (R), with no finiteness hypothesis on the proposed array.
These are shearedCount_recurrence and slitRecurrence_unique.
The theorems L_of_slitRecurrence and J_of_slitRecurrence read its two
endpoint coefficient arrays back into the independently defined L and J.

## 4. Cubic construction and coefficient evaluation

We work first in Q[[x]]. The construction and coefficient evaluation below
are independent of the walk counts. Put T(t)=A(t^3), where A is constructed
below. Thus T=1+4t^3 T^3. The walk identification is proved in sections 5–7.

Let f=1+4xf^3 and write D for the formal derivative. Put q=1-12xf^2.
Its constant coefficient is 1, so q is nonzero. Differentiating once and twice
gives

    q Df=4f^3,
    q D^2f=24f^2 Df+24xf(Df)^2.                         (8)

These are cubic_first_derivative and cubic_second_derivative. In particular,

    q^3 D^2f=24f^2(4f^3)q+24xf(4f^3)^2.

Using these identities to multiply away q^3, and using 4xf^3-f+1=0, gives

    (2x-54x^2)D^2f+(3-108x)Df-12f=0.                  (9)

More explicitly the multiplied left side is

    (-12f-12f^2+48xf^4)(4xf^3-f+1),

which vanishes. Thus cancellation is justified in the power series domain.
Similarly, for g=f^2, the product rule Dg=2fDf and
D^2g=2(Df)^2+2fD^2f give

    (2x^2-54x^3)D^2g+(5x-162x^2)Dg+(1-48x)g-1=0.     (10)

After multiplication by q^3, the left side is

    (-1-f-12xf^2-8xf^3+48x^2f^5)(4xf^3-f+1).

All identities and cancellations here are checked in
KrewerasCubicDifferential. No coefficient formula is used to obtain them.

For theta=xD define E(a,b)h=a theta(h)+bh. Its coefficient in degree m is
(am+b)[x^m]h; this is coeff_eulerLinear. Equations (9)-(10) say

    E(2,1)E(1,0)f = 6x E(3,1)E(3,2)f,
    E(2,1)E(1,1)g-1 = 6x E(3,2)E(3,4)g.

Taking degree m+1 yields, for every m>=0,

    (m+1)(2m+3)[x^(m+1)]f =
        6(3m+1)(3m+2)[x^m]f,
    (m+2)(2m+3)[x^(m+1)]g =
        6(3m+2)(3m+4)[x^m]g.                          (11)

The second identity's constant -1 has no contribution at degree m+1.
KrewerasCubicCoefficients proves these extractions including m=0.

Existence is independent of the formulas: define a_0=1; recursively define
a_(n+1)=4[x^n](sum_(i<=n) a_i x^i)^3.
Only strictly smaller indices are referenced. Set A=sum a_n x^n.
The coefficient of a product in degree n only uses coefficients of degrees
at most n, proved as coeff_pow_congr_upto. Consequently A=1+4xA^3
(ternary_cubic). Since its constant term is 1, the two recurrences (11)
determine its coefficients and those of A^2. The factorial expressions
evenProduct and oddProduct/2 have the same starting values and satisfy (11),
as proved in the inherited product-recurrence module. Induction gives

    [x^m]A = 4^m (3m)!/[m!(2m+1)!],
    2[x^m]A^2 = 4^(m+1)(3m+1)!/[m!(2m+2)!].           (12)

These are ternary_coeff and ternary_square_coeff. The same recurrence proves
cubic_unique. Applying coefficients to A=1+4xA^3 now also proves the
all-index ternary convolution for the explicit factorial numbers, and
applying coefficients to A^2 proves the binary convolution relating the
two products. Thus no convolution or Lagrange theorem is assumed.
KrewerasTernarySeries contains existence, uniqueness, (12), and both
convolution theorems.


## 5. One-sided formal square roots and the line candidate

This is a specialization of the slit-plane factorization method of
Bousquet-Mélou, *Walks on the slit plane: other approaches*,
[Lemma 11 and Theorem 12](https://arxiv.org/html/math/0104111).
The general factorization theorem is not imported into Lean: the explicit
kernel factors below and the full endpoint recurrence in section 6 supply
the needed specialization. Our walks may revisit the origin; accordingly,
our line series includes the loop factor (B0 B+ in that paper's notation),
whereas its origin-avoiding bilateral slit-plane series is B+.

All series in this section are in Q[z,z^-1][[t]], implemented as
PowerSeries (LaurentPolynomial Q). At each t degree a coefficient is a
finite Laurent polynomial. In this section T denotes its scalar inclusion
in that ring. Set

    K = (1-tz)^2-4t^2/z,
    Kminus = 1-4t^2 T^2/z,
    Kplus = 1+(-2t T^2+4t^4 T^4)z+t^2 T^2 z^2.

For any p with zero t-constant coefficient, substitute p into the binomial
series of exponent 1/2 and -1/2. The binomial addition identity proves
that these series, denoted sqrt(1+p) and invsqrt(1+p), have t-constant
coefficient 1, square 1+p in the first case, and multiply to 1.
Every substitution is t-adically legitimate because p has constant
coefficient zero. This is formalSqrt_sq and formalInvSqrt_mul.

Square roots with t-constant coefficient 1 are unique, even over a
commutative Q-algebra with zero divisors: if f^2=g^2 then
(f+g)(f-g)=0, and f+g is a unit because its constant coefficient is 2.
The map_formalSqrt and map_formalInvSqrt results follow by this uniqueness
and uniqueness of inverses.

Let Q=sqrt(K), N=sqrt(Kminus), H=sqrt(Kplus), and let Hinv and Ninv be
their constructed inverses. The polynomial identity slit_kernel_factor,
using T=1+4t^3 T^3 and z*z^-1=1, gives

    T^2 K = Kminus Kplus.
    T Q = N H.                                          (F)

The second equality follows from the first by square-root uniqueness,
not by choosing a kernel root of negative valuation.

To justify all Laurent support assertions, construct the corresponding
binomial substitutions first in Q[z][[t]]. The polynomial input for H is
(-2t T^2+4t^4 T^4)z+t^2 T^2 z^2. For N it is -4t^2 T^2 z, followed
by the Laurent embedding z -> z^-1. Mapping preserves the constructed
roots and inverses. Consequently H and Hinv have only nonnegative
z exponents, while N and Ninv have only nonpositive exponents.
Evaluating those polynomial inputs at z=0 gives zero; hence all four
roots/inverses have scalar Laurent coefficient exactly 1.

Define

    F = T Hinv.                                         (C)

This is lineCandidate, an algebraic definition independent of the walks.
Its z support is nonnegative and its scalar coefficient is T.
Multiplying (F) by Hinv yields QF=N. Therefore

    F = N+(1-Q)F,
    F = 1 + [z^>=0]((1-Q)F).                            (P)

Here the last equality is meant coefficientwise; N has no positive
Laurent coefficient and its zero coefficient is 1. The formal theorem
lineCandidate_projected states (P) at every t degree and integer
z exponent. No general projection or canonical-factorization theorem
is needed.

## 6. A full endpoint candidate and its identification with walks

Construct M by coefficient recursion, starting at constant coefficient 1,
so that

    M = 1+tz M+(t^2/z)M^2.                              (M)

The coefficient at t^(n+1) is read from
z M_trunc + t z^-1 M_trunc^2 in degree n, where M_trunc uses only
already constructed coefficients through n. Product coefficients in
degree n use only those indices. This proves motzkin_equation.
M is therefore an algebraic series constructed without assuming an
excursion bijection.

The expression 1-tz-2t^2 M/z has constant coefficient 1. Squaring it and
using (M) gives K, so square-root uniqueness gives

    Q = 1-tz-2t^2 M/z.                                  (Q)

Now define rows for k>=0 by

    S_k = F (t M/z)^k,
    S_(-k) = F (t M)^k.

The two definitions agree at k=0. Their t-constant coefficients are 1
for h=0 and 0 otherwise. For h not zero, multiplying (M) by the
appropriate common factor immediately gives

    S_h = tz S_h+t S_(h+1)+(t/z)S_(h-1).                (S)

For example at h=k+1>0 the common factor is
F(tM/z)^k(t/z); at h=-k-1 it is F(tM)^k t.
These are upperRow_recurrence and lowerRow_recurrence.
At h=0, equations (P) and (Q) give

    F = 1+[z^>=0](tzF+t S_1+(t/z)S_(-1)).              (S0)

Set b_d(h,r)=[t^d z^r]S_h. A Laurent monomial z^i shifts coefficient
r to r-i, and multiplication by t shifts d+1 to d.
Thus (S) gives the nonzero-height part of (R); (S0) gives its
height-zero part, with negative r coefficients zero. The constant
coefficient assertions give the initial condition in (R).
The theorem candidateCount_recurrence proves the entire recurrence,
including all signs of h, d=0 and r=0. By uniqueness,

    b_d(h,r)=a_d(h,r) for every d,h,r.

This is an equality with actual finite walk cardinalities, not a change
of their definition. Since S_0=F and [z^0]F=T, it proves

    L=T                                                 (L)

as origin_series. The adjacent endpoint has h=-1,r=0 and S_(-1)=tFM.
Consequently J=t[z^0](FM). This also follows directly by reading
J_of_slitRecurrence; no last-visit bijection is assumed.

## 7. Adjacent extraction

To extract one negative Laurent coefficient of N, work in the polynomial
model n(z;t)=sqrt(1-4t^2 T^2 z). Its z-constant coefficient is 1.
For polynomial-time series p,q, extraction of z^1 obeys

    [z^1](pq) = [z^0]p [z^1]q + [z^1]p [z^0]q.

This identity follows from the two terms of the polynomial product
coefficient in degree one, followed by the finite t-degree convolution.
Applying it to n^2=1-4t^2 T^2 z gives 2[z^1]n=-4t^2 T^2.
Reflecting z to z^-1 proves, at every t degree,

    [z^-1]N=-2t^2 T^2.                                 (N1)

This is negativeRoot_adjacent.

Use QF=N and (Q), and multiply by z. Ring algebra gives

    2t^2 FM = zF-t z^2 F-zN.                            (A)

The first two terms have zero scalar Laurent coefficient because F has
no negative z exponents. By (N1), scalar extraction gives
2t^2[z^0](FM)=2t^2 T^2. In Lean we extract degree d+2 first;
this reduces directly to 2[t^d z^0](FM)=2[t^d]T^2, and cancellation
takes place in Q. Hence

    [z^0](FM)=T^2,     J=tT^2.                          (J)

These are motzkin_candidate_scalar and adjacent_series. Together
(L) and (J), through literal_iff_original_series, prove the
unconditional literal endpoint mathdb346681.

## 8. Assembly of the literal product

The endpoint bijections (7), L=T and the first formula (12) give (1). The odd endpoint identity (4), (7), J=tT^2 and the second formula (12) give

    E_(2m+1)^*=2[t^(3m)]T^2
      =4^(m+1)(3m+1)!/[m!(2m+2)!],

and the parity argument gives E_(2m+1)=0. These include m=0 in the odd case, giving 2 and 0 at n=1, respectively.

For n=2m, use

    (3m)!=3^m m! product_(j=1)^m(3j-1)(3j-2)

to see that the source's product equals (1). For n=2m+1 the same identity, multiplied by 3m+1, gives exactly (2). Hence **both** evacuation counts in the literal statement are proved for every n>=1.



The formal assembly includes every n>=1. It uses the proved parity split,
the actual endpoint cardinality equivalences and P_even/P_odd.
The empty-walk initial value and the n=1 odd value are included.
K_nonempty also rules out a vacuous finite-word model.

## 9. Significance and prior-art limits

The contribution claimed is the three-sector unfolding from domino ideals
of V x [n], with its two exact endpoints, and its use in this proof of
both source formulas. The slit-plane enumeration uses established
factorization ideas. The coefficient-array verification is an economical
formal route to those ideas; it is not a new general slit-plane theorem.
This result does not address the separate promotion cyclic-sieving
Conjecture 6.2. A complete formal proof establishes correctness of the
stated formal definitions and theorem, not exhaustive novelty.

The following prior-art paragraphs are retained verbatim from the assigned
adversarial review. They describe that review's bounded investigation,
not a new search by this implementation lane.

## Shortest published route and novelty assessment

The shortest route I found is Stanley’s domino theorem, **then the new three-sector unfolding**, then [Bousquet-Mélou, Walks on the slit plane: other approaches, math/0104111](https://arxiv.org/abs/math/0104111), Lemma 11/Theorem 12, specialized to this weighted Motzkin bridge. The source’s Lemmas/Theorem 4.12 describe evacuation geometrically but do not count these fixed points. Its ordinary order-polynomial formula does not determine the comajor generating polynomial evaluated at -1, so combining that formula with Stanley is not a shortcut.

I read the slit-plane factorization and complete-solution theorem, the definitions of loops versus walks, and the triangular example. The general theorem makes the analytic-algebraic portion standard, but it does not identify domino ideals of V×[n]. Its six-step triangular example is not this three-step directed model. One must also respect that the cited slit-plane paper’s ordinary walks exclude later origin visits: its S0=B+ contrasts with this proof’s F=B0 B+, whereas its loop series is B0. The proof independently establishes the needed convention and is correct.

After the structural bridge, evaluating the two endpoint series is a modest application of the published machinery. That is the strongest ROUTINE objection. I do **not** find a one-theorem, few-line derivation of the whole literal claim: both the parity-sector identification and the off-line endpoint extraction are required. Under the brief’s specific few-line criterion my answer to “would a specialist call this routine?” is **no**, with a borderline/modest-application caveat, not a claim of a major new general enumeration theorem.


The review screened the source/final journal, local proof-registry snapshots and citing literature; it found no matching public proof. Its limitations include unavailable Semantic Scholar/ProbXiv access, no refreshed GitHub search, and full-text screening of only part of the citation set. The review also records an earlier crawl-delay process exception. This stage made no network requests, submissions, publications, or external messages.

The additional cross-model review's prior-art/significance paragraph is retained
verbatim (a review conclusion, not a new search by this implementation lane):

> Once the unfolding is in hand, the count is a standard application of
> Bousquet-Mélou's slit-plane theory (math/0104111, Thm 12: loops = B0).
> The origin count is then essentially a citation plus a constant-term
> extraction. The real content is the unfolding: the bijection from domino
> ideals of V(n) to that walk model, including the AB/AC boundary moves gluing
> three quadrant copies. That bijection is not in Stanley, Bousquet-Mélou or
> the source. A specialist would call the full argument a modest but genuine
> new proof, not a few-line corollary. I found no one-theorem route.


## 10. Certificate and reproducibility

The packet contains every source definition and bridge in 61 modules.
LEAN-SOURCE-APPENDIX.md contains them all, in import order and byte-identical
to src/. PINS.json records Lean 4.34.1, the Mathlib revision and binary hashes.
The final transitive axiom output for origin_series, adjacent_series and
mathdb346681 is exactly

    [propext, Classical.choice, Quot.sound].

Compilation and independent kernel checking use the pinned 32 GiB runner
with its unchanged memory, CPU and 140-second outer guards.
REPORT.md and FINAL-VALIDATION.json record the completed replay receipts
and the honest limits of trusting pinned upstream Mathlib oleans.
The numerical preflight checked the intermediate identities through time
60, including twenty nonzero coefficients of each endpoint. None of its
output is a premise of a Lean theorem. Nothing was submitted or published.

## Appendix: original reviews’ public-source audit text

The following two excerpts are verbatim historical review text; their dates,
access limits and process qualifications remain attached to the original reviews.
They are not a refreshed search by this lane.

### Adversarial review

## Prior-art search and what was unreachable

* Independently searched the specified Principia and mio-qwq clones by id, source identifier and Kreweras, plus omega and openai/math registries. There is no matching resolution. Mathematical hits in omega concern Chapoton–Han’s unrelated Kreweras polynomials, arXiv:2001.01449; raw numeric coincidences were excluded. See archive-hits.txt and archive-mathematical-hits.txt. These are local snapshots, not refreshed registry heads; no git was run.
* Downloaded arXiv abstract, latest PDF, recent math.CO listing, and the source-month listing. The abstract history ends at v4 in September 2021. Journal metadata was independently obtained from Crossref and OpenAlex. No later source version is advertised.
* OpenAlex returned 18 citing records; titles and available abstracts were screened (openalex-citations.json, citing-paper-screen.txt). One untitled record is a duplicate-looking Tableau evacuation record. Read relevant full-text passages from Tableau evacuation and webs (2109.04989), Order polynomial product formulas and poset dynamics (2006.01568), On the Order of P-Strict Promotion on V×[ell] (2308.08757), Rotation-invariant web bases (2306.12501), Cyclic sieving phenomena for trees and tree-rooted maps (2512.18656), and Webs and smooth components of two column Springer fibers (2602.16910v2, September 2026). None supplies this fixed-count result. The tableau paper explicitly separates its model from V(n); the P-strict paper establishes order; the trees paper still cites Conjecture 6.2 as conjectural. Also read the relevant passages of Promotion permutations for tableaux (2306.12506) and Promotion permutations and the Robinson–Schensted correspondence (2510.07744); these develop promotion permutations of tableaux and cite Hopkins–Rubey as background, without the literal V(n) evacuation enumeration. Other citation records about toric promotion, billiards and degree-two web bases were screened by metadata/abstract only, not read in full.
* Read Gatzweiler–Krattenthaler (2502.06032), especially Corollary 10: it proves polynomial positivity in Conjecture 6.2, not either evacuation count in 6.3. Do not label this PUBLIC on that basis.
* Web searches included “Kreweras evacuation formula conjecture”, “Promotion of Kreweras words conjecture 6.3 proof”, “Kreweras self-evacuating”, “Kreweras domino tableaux”, “evacuation slit plane”, and combinations with Bernardi/Mishna/Patrias/Pechenik and 2026. No matching public proof was found. The MathOverflow promotion-order result and web/rotation discussions concern different assertions.
* Semantic Scholar API returned HTTP 429; no retry/bypass. ProbXiv robots returned HTTP 402; the site was not fetched. MIT’s robots endpoint returned 403; its author PDF was not fetched; Stanley’s arXiv version was independently available. The arXiv export API was not queried in this review (the assigned author audit reports an earlier successful keyword query). No new GitHub search calls were made, preserving the candidate’s two-call allowance already used by the author; this is a search limitation, not an independent refreshed GitHub absence claim.

Process exception: I read robots.txt before direct domain fetches, and honored all explicit path refusals/HTTP refusals. However the initial arXiv downloader checked path permission without honoring its Crawl-delay: 15. Subsequent additional downloads were spaced at least 16 seconds. I cannot undo the initial delay violation and record it explicitly as PROCESS_CRAWL_DELAY_MISSED. This does not alter the mathematical evidence.

No search establishes exhaustive novelty. In particular, not all 18 citing full texts were read and Semantic Scholar/ProbXiv could not be checked directly.


### Cross-model confirmation, MathDB 346681

**Public.** I searched the omega issues by arXiv id, keywords, authors and record id; the only hit was an unrelated Chapoton issue. The Principia clone and its id list have nothing. Web searches for a proof of Conj 6.3, self-evacuating Kreweras words, 2025-26 work and the sequence terms found nothing. The nearest work is Gatzweiler-Krattenthaler, which addresses Conj 6.2 positivity only. OEIS search and the arXiv export API are both blocked by robots.txt, so I did not query them.

