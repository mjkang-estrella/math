# R019 — Attained complete equality without a scalar coefficient channel

**Accepted as the thirteenth substantial finding.** The unchanged [I287 proof](../experiments/i287_crouzeix_repeated_support/analysis.md) passes [I291 independent proof review](../reviews/i291-crouzeix-counterexample-proof.md) without repairs and [I292 independent contribution review](../reviews/i292-crouzeix-counterexample-contribution.md) as SUBSTANTIAL. The parent read both full reviews and their supporting analyses, checked the recorded hashes and compared the construction with the cited antecedents. This is written mathematical validation, not a formal proof certificate or a worldwide priority claim.

## Exact theorem

Let N be the real 6 by 6 matrix with the following nonzero entries, all others zero:

    N12=6/5,       N14=sqrt(14)/5,
    N23=8/5,       N43=-3sqrt(14)/20,
    N45=5/4,       N56=sqrt(2).

Define the 2 by 2 matrix polynomial

    P(z) = [ 3z²/4          sqrt(7)z³/4 ]
           [ sqrt(7)z/4    -3z²/4       ].

Use Euclidean operator norms and base-first evaluation P[N]=sum_k N^k tensor C_k. Then N is unitarily irreducible, its numerical range is the closed unit disk, and

    max_|z|<=1 ||P(z)|| = 1,        ||P[N]|| = 2.

Nevertheless, for every pair of constant complex unit vectors u,v in C²,

    ||(v*P u)(N)|| <= sqrt(849)/16 < 2.

Thus the scalar coefficient channel conclusion of [R016](R016-complete-crouzeix-equality.md), valid for every specified equality witness through base dimension four, does not extend to arbitrary dimensions. The example retains a disk numerical range. It does not disprove the separate disk-rigidity conclusion.

## Proof

Put h=(3,2,1,2,1,0). Every nonzero N_ij has h_i-h_j=1, so conjugation by diag(exp(i theta h_j)) rotates N by exp(i theta). Reorder Re N as (1,3,5 | 2,4,6). It becomes the block matrix with diagonal blocks zero and off-diagonal blocks C,C*, where

    C = [ 3/5    sqrt(14)/10     0         ]
        [ 4/5   -3sqrt(14)/40    0         ]
        [ 0      5/8            1/sqrt(2) ].

For a=(sqrt(2)/2,-3sqrt(2)/8,-sqrt(7)/8), direct multiplication gives CC*=I-aa* and ||a||²=57/64. The singular values of C are 1,1,sqrt(7)/8. Hence every support pencil Re(exp(-i theta)N) has eigenvalues 1,1,-1,-1,sqrt(7)/8,-sqrt(7)/8. Its support function is constantly one, proving the numerical-range assertion.

On the unit circle the two columns of P are orthogonal unit vectors. The maximum principle applied to scalar matrix elements gives the disk norm one. Put

    ell=(sqrt(7)/5)e2-(3sqrt(2)/5)e4,
    x=(e3 tensor f1+e6 tensor f2)/sqrt(2),
    y=(e1 tensor f1+ell tensor f2)/sqrt(2).

Here ell is a unit vector and N ell=0. Direct evaluation gives P[N]x=2y. To certify the upper bound and uniqueness, grade the tensor basis by h_i+g_j with g=(0,1). Every term of P[N] raises this grade by two. The grade dimensions are (1,3,4,3,1). The outer nonzero blocks have rank one and squared norm 337/128. The middle block, in input basis (e3 f1,e5 f1,e6 f2) and output basis (e1 f1,e2 f2,e4 f2), is

    B = [ 9/8           3sqrt(14)/16       7/8          ]
        [ 2sqrt(7)/5    0                 0            ]
        [-21sqrt(2)/80  5sqrt(7)/16       -15sqrt(2)/16 ].

The vector (1,0,1)/sqrt(2) is a squared-singular-value-four eigenvector. On its orthogonal complement, in basis ((1,0,-1)/sqrt(2),(0,1,0)), B*B has matrix

    [ 67/64          33sqrt(7)/128 ]
    [ 33sqrt(7)/128  301/256       ].

Its trace is 569/256 and determinant 49/64. Consequently the complete list of nonzero squared singular values of P[N] is

    4, 337/128, 337/128, (569+33sqrt(113))/512,
    (569-33sqrt(113))/512.

The last two are below 337/128. Thus the top singular input line is exactly Cx, the top output line is Cy, and ||P[N]||=2.

Both x and y have two equal Schmidt coefficients. Every unit product vector zeta tensor u therefore has squared overlap at most 1/2 with x. The preceding complementary norm bound yields

    ||P[N](zeta tensor u)||²
       <=4/2+(337/128)/2=849/256.

Applying the contraction I tensor v* and taking the supremum over zeta proves the assertion for every complex unit u,v. No real-vector restriction or coordinate-only test is used.

Finally N³N*³=(7/4)e1e1*. Any orthogonal projection commuting with N and N* therefore maps e1 either to zero or to e1. The vector e1 is cyclic for the star algebra: N*e1=(6/5)e2+(sqrt(14)/5)e4, N*²e1=(3/2)e3+(sqrt(14)/4)e5, and N*³e1=(sqrt(7)/2)e6. The e2,e4 component obtained by applying N to N*²e1 has a nonzero component along ell, orthogonal to N*e1. Hence e2,e4 are in the cyclic span. Also N*ell=(sqrt(7)/2)e3-(3sqrt(2)/4)e5 is independent of N*²e1: the determinant of these two coefficient vectors is -2sqrt(2). All six coordinate vectors are in the cyclic span. A commuting projection is therefore zero or identity, proving irreducibility. This completes the theorem.

## What the construction adds

The matrix is an old Li–Spitkovsky–Shukla example, reproduced in [Lawrence, Section 4](https://arxiv.org/html/1809.02779v2#S4). No novelty is assigned to its disk or repeated support spectrum. The proposed increment is a compatible original-matrix norming channel with finite polynomial attainment and a uniform obstruction to every constant coefficient compression.

The stipulated [direct complete-Crouzeix proof](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026) and [structural companion](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-complete-Crouzeix-theorem-September-23-2026) motivate the original-resolvent equality system. For this example it is genuinely saturated: the mass-two positive boundary field has rank four, D=XX*-YY* has inertia (2,2,2), and H^(1/2)DH^(1/2)=0. The full proof and I291 check give the exact zero-residual certificate. This realizes the rank-two alternative that the dimension-four argument excludes.

The I292 contribution analysis independently derives the additional old-family compatibility equations b²(1-c²)=1/2 and xi²=eta²=1/2. It compares the actual source rational endpoint construction, [ACV's equality results](https://arxiv.org/html/2608.27346v3), and standard inner realizations. The factorization P(z)=z diag(z,1) R diag(1,z) is standard and credited. Its ordinary contraction-state realization does not itself provide this original N, its attained norming lines or the compression obstruction. Those comparisons, not the length of the computations, support the substantiality decision.

## Validation and boundaries

- I291: independent proof PASS on the original analysis SHA256 `8f8eb9a51203ec949356a1e92913447b56766e68496ec2384003c24430bbcd0b`, without repairs.
- I292: independent contribution SUBSTANTIAL, including a constructive comparison with old LSS, inner realization and rational endpoint operations. All 32 available input records and five returned output hashes were verified by the parent.
- The original LSS full article was inaccessible; Lawrence's primary reproduction was read. This is a material priority-search limit, not a claim that the inaccessible article contains no relevant operation.
- No smallest possible dimension, classification of all six-dimensional witnesses, nondisk counterexample, quantitative near-extremizer theorem or strict scalar-supremum gap is claimed. A different scalar polynomial is not a constant coefficient compression of this specified P.
- The optional I287 statement that each scalar polynomial separately misses equality uses credited scalar rigidity; it is not needed here and is not another finding. Nonpolynomial Schur-jet limits remain unexcluded.

Candidate commit `8c9e63ee`; independent proof integration `01b7d06c`; contribution integration `7e0edfe7`. This acceptance has its own commit. **Thirteen accepted; seven remain toward twenty.**
