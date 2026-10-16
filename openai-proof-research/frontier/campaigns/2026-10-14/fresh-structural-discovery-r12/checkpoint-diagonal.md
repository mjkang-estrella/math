# Q4 checkpoint: the actual common-diagonal problem

For G=Spin(2n), write c(a,b;t)=dim Hom_G(V(t),V(a) tensor V(b)).
Complete reducibility and Schur's lemma give exactly

 dim(V(a) tensor V(b) tensor V(c) tensor V(d))^G
   = sum_t c(a,b;t)c(c,d;t*).

At scale N a nonzero summand supplies eta. The rational weight eta/N
need not be a weight, and even if it is a weight it need not be in
L=a+b+Q. Total external root congruence makes the two required central
cosets compatible: if t in L then c+d+t in Q. This does not supply t.

Let P(a,b) be the real dominant moment polytope of sums of compact
orbits a,b. Berenstein--Sjamaar 3.2.1--3.2.2 identify its rational
points with occurrence after some common dilation. Thus, using the
stipulated triple saturation, Q4 is exactly the following lattice
intersection assertion on the ORIGINAL inputs having scaled occurrence:

 [P(a,b) intersect (P(c,d))*] intersect (a+b+Q) != empty.

Here is the full reverse bridge, without assuming a lattice point.
Suppose a point t in that intersection ALSO belongs to a+b+Q. It is then
a dominant weight. Every simple reflection changes a weight by an integral
multiple of a root, so W acts trivially on P/Q, and t*=-w0(t) is congruent
to -t. Thus a+b-t and c+d-t* both belong to Q, the latter because the
external total belongs to Q. Berenstein--Sjamaar gives occurrence of V(Mt)
in V(Ma) tensor V(Mb) for some M, and occurrence of V(Lt*) in V(Lc)
tensor V(Ld) for some L. The stipulated triple theorem applies separately
WITH THESE INTEGRAL LABELS and congruences, giving c(a,b;t)>0 and
c(c,d;t*)>0 at scale one. Their product is a positive summand in the
four-invariant formula. Conversely, an unscaled four-invariant supplies
such an integral t by its own decomposition and the necessary central
character congruence. A dilated four-invariant supplies only eta/N in
the real intersection. This proves the claimed exact remaining operation,
without assuming that eta divides or has the unscaled congruence.

The forward Cartan-power implication is classical and works for any
number of tensor factors. Its proof appears in candidate.md.

A generic normality argument does not prove this: the cones
 C1={(A,z): A>=0, 0<=2z<=A},
 C2={(B,z): B>=0, B<=2z<=2B}
have dilation-saturated lattice semigroups of all their integer points.
At A=B=1 their fibers are [0,1/2] and [1/2,1], each containing an integer,
but their intersection {1/2} does not. At A=B=2 their common fiber has
z=1. This refutes the indicated normality/projection inference only;
these cones are NOT asserted to be tensor cones or an associative fusion
semiring. It does not refute Q4.

An actual Spin(8) shortcut diagnostic uses a=b=omega1=e1 and
c=d=omega4=(e1+e2+e3+e4)/2. All four modules are self-dual (-1 is in W(D4)),
so pair contractions supply an invariant. Total sum is (3,1,1,1), in Q(D4).
Replacing V(a) tensor V(b) by its Cartan summand V(2e1) destroys it:
every weight of S+ tensor S+ has first coordinate at most 1, whereas
2e1 has first coordinate 2. Thus Hom(V(2e1),S+ tensor S+)=0.
The S+ weight description is the standard half-spin model, not a new
representation theorem. A common unrestricted diagonal does exist (0).
This is a counterexample to that Cartan replacement, not to Q4.

The source's own tail:fractional remark already gives the separate
warning against dividing an arbitrary diagonal: V(2e1) has a cubic
invariant, but V(e1) does not. In the four-vector problem at N=2, eta=2e1
can therefore be a selected diagonal; eta/N=e1 is outside 2e1+Q. Other
diagonals work at scale one. This warning is credited to the source,
not nominated as a new result.
