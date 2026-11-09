Mathematical work and remaining gaps
===================================

These are ordinary mathematical attempts and diagnostic models, not certified endpoints.
No global novelty claim is made. The original corpus statements are in extracted.json;
source version anchors and hashes are in outputs/version-anchors.json.

362890: canonical decomposition and coefficient route
----------------------------------------------------

Let S_n(z) count nonempty separable permutations by left maxima and I_n(z)
count direct-indecomposable ones. Let a_j = I_j(1). Decomposition at the first
canonical direct block gives

    S_n(z) = I_n(z) + sum_{j=1}^{n-1} I_j(z) S_{n-j}(z).

Decomposition of a direct-indecomposable permutation into canonical skew
blocks, taking the first skew-indecomposable block and the remaining nonempty
separable suffix, gives

    I_n(z) = z [n=1] + sum_{j=1}^{n-1} a_j S_{n-j}(z).

Complement exchanges direct and skew indecomposability, hence the same
univariate a_j is used in the second identity. For skew sum, all left maxima
are in the first block; for direct sum their numbers add. The code implements
these two identities and independently verifies the first seven distributions
by enumerating every permutation avoiding 2413 and 3142. The full serial run
through n=250 has no peak-two or declining-tail violation.

Writing A(t)=sum a_n t^n and S(t,z)=sum S_n(z)t^n, the equations reduce to

    I = zt + A S,       S = I(1+S),
    S = zt + (zt+A) S + A S^2.

This supplies a concrete full-scope proof route: prove coefficientwise
[t^n z^k]S >= [t^n z^{k+1}]S for n>=3,k>=2, together with the rising 1-to-2
comparison. Positivity of coefficients of S does not imply these differences.
The source's own radical generating function is compatible with these
equations but does not give the needed inequalities immediately. This lane
did not close the uniform difference inequality or formalize the canonical
bijections. Omega's current peak-three files address irreducible distributions
(Conjecture 2), not this full-class Conjecture 1, and explicitly retain a tail gap.

353384: lattice sums, structural perturbations
--------------------------------------------

For a connected n-vertex graph the signed edge roots are e_u-e_v and e_v-e_u.
The diagnostic enumerates sums of at most t roots, t=0,1,2,3. The root coordinate
range is [-3,3]; balanced base seven on n-1 independent coordinates is injective
on this range, so integer encoding introduces no collisions. The interpretation
as all lattice points of tP uses the standard integer decomposition property
of symmetric edge polytopes; that semantic theorem is not formalized here.
The conversion from L(t) to h* and gamma is

    h_i = sum_{j=0}^i (-1)^j binom(n,j) L(i-j),
    gamma_i = h_i - sum_{j<i} gamma_j binom(n-1-2j,i-j).

All 367 logged cases have connectivity at least three (tested after every
vertex deletion of cardinality 0,1,2). The split-interval comparison enumerates
all choices of the three-vertex part. Eight clique-side masks are tested at
each order; adding an independent-side edge and selected crossing-edge swaps
probe the first departures from the proposed zero family. All checks agree.
These are structured and random cases, not a canonical graph census, and no
claim that they exceed a numerical source ceiling is justified: the source
only says small k,n. The k=2 source theorem does not settle k=3. A structural
formula for gamma_3 under 3-connectivity remains the precise gap.

354662: wiring words and antipodal coloring
------------------------------------------

A reduced word for the longest permutation reverses each pair of wires exactly
once. Record the crossing vertices along each wire and join consecutive ones
cyclically. This is the crossing graph on the projective arrangement, whose
3-colorings correspond to antipodal 3-colorings of its great-pseudocircle lift.
Reduced words are sampled by choosing a currently increasing adjacent pair
until the reverse order is reached. This sampler is reproducible but biased.
An exact backtracking coloring solver uses maximum saturation and color
symmetry reduction. Every successful coloring is found by backtracking;
a node limit produces unknown, never false. No failed coloring was proved.

The first run uses 500 samples at every n=7..18; the second uses 50 at every
n=19..40. It expands the number of wires substantially beyond the source's
introductory exhaustive range 11 for the older coloring question. It does not
establish a new verified bound, nor cover all abstract pseudocircle arrangements.
General parts (a),(b) have not been searched. The latter has a sufficiently-large
quantifier, so one small exceptional arrangement would not resolve it.

355432: complete signature enumeration and classical obstruction
---------------------------------------------------------------

Let v_i(j) count permutations of length i with the specified initial sign word
whose last entry has rank j. Appending an ascent takes prefix sums, appending
a descent takes complementary prefix sums. Enumerating the binary recursion
therefore evaluates every signature exactly without enumerating n! labelings.
If the sign word equals its reverse with signs negated, each unrooted oriented
path is counted twice; otherwise its count equals its signature count. This
matches the source's path-as-arc-set convention and its Theorem 4.
All signatures through n=25 satisfy the intended bound (printed for n>=5).
The signed-sum typo in the displayed source conjecture is not exploited.

The even case is already Niven/de Bruijn under this bridge. The classical
Ehrenborg–Mahajan paper proves that among words with a single double block,
the best location is (1,2,1,...,1), Corollary 5.5. The remaining global odd-case
comparison, including the halved alternating word, was not established here.
The abundant classical ascent/descent literature is a material subsumption
risk, not an excuse to call the finite extension a discovery.

359681: modular q-bracket rank experiment
-----------------------------------------

The model uses regularized shifted sums

    p_l(lambda) = sum_i ((lambda_i-i+1/2)^l-(-i+1/2)^l)
                  -(1-2^{-l}) B_{l+1}/(l+1).

For each stationary weight partition with parts>=2 it evaluates products of
p_{part-1} on all partitions of d, d=0..30, modulo 1000000007. It forms columns
from those partition sums and performs exact modular Gaussian elimination.
The common Euler product is invertible and factorial scalings of columns are
nonzero at this prime, so omitting them preserves rank in this model. Every
even weight through 30 attains dim QM_k, including weights beyond the source's
explicit low-weight examples. This is a finite non-finding and leaves the
full GW-correspondence/normalization bridge uncertified here.

A tempting use of van Ittersum's symmetric Bloch–Okounkov surjectivity theorem
fails at the domain: its algebra S of symmetric functions in part multiplicities
is not automatically the shifted-symmetric algebra used for stationary descendents.
No routine full-scope bridge is asserted. An all-weight rank proof is still needed.

355534 and 358772: further sustained diagnostics
------------------------------------------------

For 355534, the independent integer transcription of Appendix B enumerates
all paths, computes degree and area, selects maximal paths by the closest
nonendpoint diagonal position, and compares the full signed-string polynomial.
The logs enumerate all 104 parameter pairs and their path counts. A test of
one or two evaluations of q,t would be insufficient; this checks every coefficient.
No failure was found, and no infinite cancellation bijection was produced.

For 358772, Appendix A.3 permits row/column triangularization. In the standard
root model each column of w is a signed interval of simple roots between
w(i) and w(i+1). A nonsingular matrix is permutable triangular only if some
column is singleton. Removing that column and its unique row preserves the
question recursively; distinct singleton columns cannot conflict in a nonsingular
matrix. All permutations through n=9 were tested, with precisely the separable
ones passing. No other Specht shape was computed and no KL-basis identification
is formally certified here. This search cannot certify the universal converse.
