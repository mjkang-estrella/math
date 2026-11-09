# Exact primary-body locations
All locations below refer to frozen extracted text. PDF page is one-based form-feed count; full bodies are retained beside text. Excerpts are evidence, not a substitute for proof analysis.

## primary/1505.00355v2.txt: Theorem 6.; PDF page 2; text line 110
```text
Theorem 6. ([19] or [17, Ch. II.]) Let {γk }k=0 be a sequence of real numbers. The following are equivalent:
            ∞
   (i) {γk }k=0 is a multiplier sequence;
  (ii) (Algebraic characterization) for each n ∈ N0 ;
                                          n  
                                          X   n
                                                 γk xk ∈ L − PI;
                                              k
                                                 k=0

   (iii) (Transcendental characterization)
                                                    X
                                                    ∞
                                                      γk
                                                               xk ∈ L − PI.
                                                          k!
                                                    k=0
                                  ∞
Definition 7. Let T        = {γk }k=0 be a sequence of real numbers.              For n ∈ N0 , we definite the nth Jensen
polynomial associated with the sequence T to be
                                                                        n  
                                 
```

## primary/1505.00355v2.txt: Example 20.; PDF page 9; text line 722
```text
Example 20. The sequence k 1/20 /k! k=0 is not a multiplier sequence. In fact, if we consider the Jensen
polynomials associated with
                                                    X
                                                    ∞
                                                        k 1/20 k
                                            f (x) =           x
                                                          k!
                                                                k=0
we find that the sixth Jensen polynomial
                                    15x2      10x3        5x4          x5          x6
                      g6 (x) = 6x +  19/20
                                           + 19/20 +          9/10
                                                                   + 19/20 +
                                   2         3         40 · 2       45        120 · 619/20
has has only four real zeros, along with a pair of non-real zeros. This phenomenon persists for small s, but
appears to change when s = 1/2. In this case all the Jensen polynomials that we tested have only real zeros.
                                                                              
```

## primary/1505.00355v2.txt: Problem 39.; PDF page 16; text line 1305
```text
Problem 39. Determine whether the sequence { k!k } is (a) a multiplier sequence (b) a CZDS (cf. Definition
4).
                                   n √ o∞
                                      k
    We remark that if the sequence   k!    is a multiplier sequence (or a CZDS), then the sequence
  √                                           k=0
     k ∞
{ (2k)! }k=0 is also a multiplier sequence (or a CZDS). Indeed, it follows from the Legendre Duplication
                               √
                                 π         k!
Formula [2, p. 71] that k              =        . Now by Laguerre’s theorem ([7, Theorem 4.1 (3)]), the se-
                          4 Γ(k + 1/2)    (2k)!
                1
quence {              }∞ is a CZDS and whence the above claim follows.
           Γ(k + 1/2) k=0
                                                                             1
In light of the discussion in Example 34 and the fact that the sequence {         }∞ is a CZDS, we expect
                                                                          Γ(k + 1) k=0
an affirmative answer to the following question (see also Theorem 1).
                                                    
```

## retrieval/citer1702.txt: We end this subsection; PDF page 7; text line 340
```text
We end this subsection with Theorem 6, which settles a conjecture in
[CF16, p. 1379] for s = 21 and is related to [CF16, Problem 6]. In [CF16,
                                     P √n z n
Lemma 11] it was shown that η 1 =
                                  2      Γ(n+1) n! is Hurwitz stable, that is,
                                       n≥0
all of its zeros lie in the closed left half-plane. Moreover, it was conjectured
(see [CF16, p. 1379]) that η 1 ∈ LP + . Theorem 6 verifies this conjecture
                                   2
and shows that all zeros of η 1 lie in (−∞, 0].
                                 2
                                          P ns z n          +
Theorem 6. If s > 0, then ηs (z) =            Γ(n+1) n! ∈ LP .
                                       n≥0

1.3. Concluding remarks. In this paper we have seen that in very special
cases (when the coefficients of entire functions contain almost only recipro-
cal gamma function terms) we can find the maximal or the exact number of
complex zeros of the entire functions in the question. However, for example
in the above mentioned conjecture of Kalmykov and Karp [KK16, Conjec-
ture 3] the coefficients are meromorphic
```

## retrieval/citer1702.txt: Proof of Theorem 6.; PDF page 11; text line 586
```text
Proof of Theorem 6. Since the coefficients of ηs are positive, we just need
to show that ηs (z) ∈ LPI or equivalently ηs (−z) ∈ LPI. The entire function
z s /Γ(z + 1) has growth order 1, it belongs to LP and has only one zero in
[0, ∞), and that is 0. Consequently by using Lemma 3 (for the function
e−z ∈ LPI), we obtain that ηs (−z) has exactly 1 nonpositive real root, and
that is 0. In other words, all zeros of ηs (−z) are strictly positive, that is,
ηs (−z) ∈ LPI.                                                               

                                     References
[ABP16] H.A. Alkharsani, Á. Baricz, T.K. Pogány, Starlikeness of a cross-product
 of Bessel functions, J. Math. Inequal. 10(3) (2016) 819–827.
[BKP16] Á. Baricz, C.G. Kokologiannaki, T.K. Pogány, Zeros of Bessel function
 derivatives, arXiv:1602.04295.
[BSY16] Á. Baricz, R. Szász, N. Yağmur, Products of Bessel and modified Bessel
 functions, arXiv:1601.01998.
[CR15] H. Chaggara, N. Ben Romdhane, On the zeros of the hyper-Bessel function,
 Integral Transforms Spec. Funct. 26(2) (2015) 96–101.
[CC06] T. Craven, G. Csordas, The Fox-Wright functions and Laguerre multiplier
 sequences, J. Math. Anal. Appl. 
```

## retrieval/citer1702v2.txt: We end this subsection; PDF page 6; text line 299
```text
We end this subsection with Theorem 6. This result is related to [CF16,
Problem
P ns 6]:    is it true that for every s ∈ R+ , there exists an m ∈ N such that
          n       +
   (n!)m z ∈ LP ? Theorem 6 verifies the case when s ∈ N0 and m = 2.
n≥0
                                           P       ns   zn     +
Theorem 6. If s ∈ N0 , then ηs (z) =             Γ(n+1) n! ∈ LP .
                                           n≥0

1.3. Concluding remarks. We have seen that in some special cases we can
find an upper bound for the exact number of complex zeros of entire func-
tions. However, for example in the above mentioned conjecture of Kalmykov
and Karp [KK16, Conjecture 3] the coefficients are meromorphic and so far
we are not aware on any result in the literature which would help to ver-
ify this conjecture. Craven and Csordas [CC06, Problem 1.2] posed the
following problem: Characterize the meromorphic function F with the prop-
          P an F (n) n
erty that       n! z is a transcendental entire function with only real zeros
          n≥0                 P an n
whenever the entire function      n! z has only real zeros. This problem is
                               n≥0
strongly
```

## retrieval/citer1702v2.txt: Proof of Theorem 6.; PDF page 10; text line 520
```text
Proof of Theorem 6. Since the coefficients of ηs are positive, we just need
to show that ηs (z) ∈ LPI or equivalently ηs (−z) ∈ LPI. The entire function
z s /Γ(z + 1) has growth order 1, it belongs to LP and has only one zero in
[0, ∞), and that is 0. Consequently by using Lemma 3 (for the function
e−z ∈ LPI), we obtain that ηs (−z) has exactly 1 nonpositive real root, and
that is 0. In other words, all zeros of ηs (−z) are strictly positive, that is,
ηs (−z) ∈ LPI.                                                               

                               Acknowledgement
  The research of Á. Baricz was supported by the STAR-UBB Advanced
Fellowship-Intern of the Babeş-Bolyai University of Cluj-Napoca. Both au-
thors wish to acknowledge the referee’s comments and suggestions which
enhanced this paper.

                                     References
[ABP16] H.A. Alkharsani, Á. Baricz, T.K. Pogány, Starlikeness of a cross-product
 of Bessel functions, J. Math. Inequal. 10(3) (2016) 819–827.
[BKP16] Á. Baricz, C.G. Kokologiannaki, T.K. Pogány, Zeros of Bessel function
 derivatives, Proc. Amer. Math. Soc. (in press).
[BSY16] Á. Baricz, R. Szász, N. Yağmur, Products of Bess
```

## retrieval/polya2110.txt: Theorem A.; PDF page 2; text line 54
```text
Theorem A. Let f (t) be a positive increasing functionR 1 for 0 < t < 1
        such that it is in the general case1 and the integral 0 f (t)dt exists.

        (A1) U (x) > 0 for 0 < x ≤ π/2, U (x) has one and onlyone simple zero
             in each of the intervals (k − 1/2)π, (k + 1/2)π , k = 1, 2, · · · ,
             and no positive zeros elsewhere. If, in addition, f (t) is convex and
             the right derivative f 0 (t) is in the general case, then U (x) has a
             unique simple zero in each of the intervals (k − 1/2)π, kπ .
        (A2) V (x) > 0 for 0 < x ≤ π, V (x) has one and only one simple
             zero in each of the intervals kπ, (k + 1)π , k = 1, 2, · · · , and no
             positive zeros elsewhere. If, in addition, f (t) is convex and has the
             limiting value f (0+) = limt→0+ f (t) = 0, then V (x)has a unique
             simple zero in each of the intervals kπ, (k + 1/2)π .

        Theorem B. Let f (t) be a positive, decreasing and concave function
                                      0
        R 1 0 < t < 1 such that −f (t) is in the general case and the integral
        for
         0
            f (t)dt exists. Then U (x) >
```

## retrieval/polya2110.txt: Theorem 2.1.; PDF page 4; text line 160
```text
Theorem 2.1. If f (t) is a positive decreasing function for 0 < t < 1 such
that it is in the general case, then V (x) > 0 for all x > 0.

Proof. On writing V (x) = π/x · S(x), where
                               Z x/π  
                                      πt
                        S(x) =      f    sin πt dt,
                                0     x

it suffices to prove the strict positivity of S(x) for x > 0. Clearly, S(x) > 0
for 0 < x ≤ π. For a positive integer m and 0 ≤ θ ≤ 1, put
                                                        
                                                      t
                      x = (m + θ)π, φ(t) = f               .
                                                   m+θ




                                       4
By decomposing the integral and changing variables, we have
                        Xm Z k     Z m+θ !
              S(x) =             +         φ(t) sin πt dt
                           k=1     k−1          m
                          m
                          X                Z 1
                      =         (−1)k+1             φ(k − 1 + t) sin πt dt
                          k=1               0
                    
```

## retrieval/polya2110.txt: 3    Method of partial fractions; PDF page 7; text line 309
```text
3    Method of partial fractions
   This section aims to revisit the method of partial fractions used decisively
in Pólya’s investigations for the sake of subsequent applications. R
                                                                      1
   For any function f (t) defined for 0 < t < 1, if the integral 0 |f (t)|dt
converges, then it is evident that Fourier transforms
                              Z 1
                    U (z) =       f (t) cos zt dt,
                    
                    
                                0
                               Z 1                  (z ∈ C)               (3.1)
                    
                    V (z) =
                                  f (t) sin zt dt
                               0

are entire functions. In consideration of the Fourier cosine series
                              ∞
                         a0 X
                 f (t) ∼   +     ak cos kπt,    ak = 2U (kπ),
                         2   k=1


                                      7
if it is assumed, for instance, that the series converges to f (t) uniformly on
every bounded subinterval of (0, 1), then termwise integrations lead to
                            ∞                             
            U (z)   U (0) X        k            1      1
                  =      +     (−1) U (kπ)         +         ,             (3.2)
            sin z     z    k=1
                                             z − kπ z + kπ

the partial fraction formula discovered by Hurwitz [14]. By using this for-
mula, Hurwitz proved that if the Fourier coefficients (ak ) alternate in sign
with a0 > 0, then U (z) has only real simple zeros and each of the intervals
 kπ, (k + 1)π contains exactly one zero, where k = 1, 2, · · · .
    From a complex analysis point
                                R 1 of view, Pólya proved that (3.2) remains
valid under the sole condition 0 |f (t)|dt < ∞. In fact, he noticed that the
residue at the simple pole kπ of U (z)/ sin z is given by

                      (z − kπ)U (z)
                 lim                = (−1)k U (kπ),     k ∈ Z,
                 z→kπ     sin z
and hence the difference between U (z)/ sin z and the series on the right side
of (3.2) is an entire function. By expressing U (z)/ sin z as a contour integral
and exploiting periodicity of sin z, he verified that the difference is bounded
in C, whence it reduces to a constant according to Liouville’s theorem. Since
the difference is an odd function, the constant must be zero, which completes
Pólya’s proof for Hurwitz’s formula (3.2).
    In a similar manner, Pólya obtained two additional formulas
                           ∞
        U (z)    U (0) X (−1)k U [(k − 1/2)π]
               =        +
       z cos z     z      k=1
                                    (k − 1/2)π
                                                                
                                       1                1
                           ×                   +                    ,      (3.3)
                                z − (k − 1/2)π z + (k − 1/2)π
                            ∞
                 V 0 (0) X (−1)k V (kπ)
                                                               
        V (z)                                    1         1
               =        +                             +           ,        (3.4)
       z sin z      z      k=1
                                     kπ       z −  kπ   z +  kπ
                                             R1
both of which are valid under the condition 0 |f (t)| dt < ∞.
    When the coefficients for k ≥ 1 keep the same sign, these partial fraction
expansions can be used in various ways to determine the existence and nature
of zeros. To explain the idea of Hurwitz and Pólya briefly, note that all of

                                       8
the partial sums are rational functions of the form
                               N                    
                          A0 X           1      1
                 SN (z) =   +     Ak         +         ,
                          z   k=1
                                       z − ak z + ak

where 0 = a0 < a1 < a2 < · · · < aN and Ak coincides with the residue at the
pole ak . Suppose, for instance, that A0 > 0 and Ak > 0 for all k ≥ 1. Then
it is elementary to see that SN(x) as a function of x > 0 decreases strictly
from +∞ to −∞ on ak−1 , ak , k = 1, · · · , N, so that it has a unique simple
zero in each of these intervals. As the possibility that the zeros of SN (z) move
towards end-points ak ’s are obviously excluded, one may conclude by letting
N → ∞ that the corresponding Fourier transform has only real simple zeros
whose positive zeros are distributed in the same way as described.
    Our analysis will be based on Wronskian inequalities. To be more specific,
let us denote the Wronskian determinant of f (z), g(z) by

                    W [f (z), g(z)] = f (z)g 0 (z) − f 0 (z)g(z).

As to Hurwitz’s formula (3.2), if we multiply by z and differentiate, where
differentiating termwise is justified due to the uniform convergence of the
derived series on every compact subset of C \ {±kπ : k ∈ N} , we obtain
                                             ∞
                                   4 sin2 z X (−1)k U (kπ) k 2 π 2
                             
                        sin z
              W U (z),          =                                  .   (3.5)
                          z            z    k=1
                                                (z 2 − k 2 π 2 )2

Since the singularities at z = 0 or z = kπ, k = ±1, ±2, · · · are easily seen
to be removable, this formula remains valid for all z ∈ C.
   Proceeding in the same way, we obtain from (3.3), (3.4)
                                ∞                       
                          2
                              X    (−1)k U (k − 1/2)π) (k − 1/2)π
   W U (z), cos z = 4z cos z                                   2  , (3.6)
                               k=1         z 2 − (k − 1/2)2 π 2
                                          ∞
                                    2
                                         X   (−1)k V (kπ) kπ
               W V (z), sin z = 4z sin z                        ,          (3.7)
                                              (z 2 − k 2 π 2 )2
                                         k=1

both of which are valid for all z ∈ C.
    For a smooth oscillatory function f (x) defined on an open interval I,
it is known in Sturm’s theory of oscillations, or readily verified otherwise,

                                         9
that if the Wronskian W [f (x), g(x)] keeps constant sign on I, 
```