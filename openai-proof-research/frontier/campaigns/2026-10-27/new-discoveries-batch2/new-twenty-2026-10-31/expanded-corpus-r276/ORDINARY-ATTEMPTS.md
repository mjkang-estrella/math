# Ordinary attempts; no qualified candidate

No Lean, solver, numerical search or graph enumeration was run. These are ordinary deductions and precise gaps, not execution assignments. All integer parameters below use the primary partition paper's conventions. No acceptance credit is requested.

## 321728: tight Latin rectangles

Read arXiv:1106.3453v1–v3 Conjecture 1 and the v3 complete-by-complete proof and boundary discussion. Put m=m0 and q=n+1. A proper q-coloring is an m by n Latin rectangle. When each row has a different missing color, the only vertices whose entire color-distance code has no coordinate 2 are the full vertices: their column contains that row's missing color. The source's conditions of distinct missing colors and no repeated full colors suffice to make the coloring locating. There are exactly m(m-1) full vertices. Therefore q>=m(m-1), and the hard boundary is n=m(m-1)-1 through n=m(m-1)+m-4. The later n range is explicitly already covered by the source's extension argument.

First route: extend the source's induction. With i completed rows, inserting missing colors successively has the lower bound n-i^2+1-2(i-1). At i=m-1,n=m(m-1)-1 this is 3-m. This is not evidence of nonexistence: the estimate fails exactly at the intended boundary. Hall completion after choosing these distinguished cells does not repair their preliminary selection. Need a simultaneous assignment with color-disjoint full vertices, not independent Hall matchings.

Second route: use a cyclic Latin rectangle. Choose distinct a_r in Z/qZ, columns j!=0, and color (r,j) by j+a_r. Row r misses a_r; when the missing color occurs in row s, its column is j=a_r-a_s. The resulting full vertex in row r has color 2a_r-a_s. Thus injectivity of (r,s) -> 2a_r-a_s on ordered distinct row pairs gives a sufficient construction. At q=m(m-1) this must biject onto Z/qZ. It is a restrictive additive design requirement; ordinary Sidon differences do not automatically give it. Even the necessary sum condition is nontrivial: the sum of these ordered-pair labels is (m-1)sum(a_r), whereas the sum of all q residues is q(q-1)/2 modulo q. No uniform design was found or asserted. Failure of this ansatz would not refute unrestricted Latin rectangles.

Third route: distinguish special cells first and complete remaining rows with matchings. This still needs a simultaneous rainbow assignment of the m(m-1) special colors, compatible across columns and with the row omissions. No theorem establishing that assignment at equality is available here. No finite obstruction, full proof, or Pi request.

## 322716: an actual partial ordinary proof, insufficient for the literal problem

Read all three arXiv versions' Conjecture 5.1 and latest Theorems 4.1–4.2. v1 allowed 1<x<=y+z; v2/v3 narrow this to y<x<=y+z, matching MathDB. The publisher request returned 403 and was not retried. The source already proves z=2, odd y, m=2y+2; specializing to that family is excluded explicitly.

For fixed positive integer L, z>1, y>z, y<x<=y+z, m>=yz+2, let A be the multiset of 3L permitted part sizes 1+jm,x+jm,yz+jm and B the multiset z+jm,y+jm,yz+1+jm, 0<=j<L. Write P_A(q)=prod_{a in A}(1-q^a)^(-1), and similarly P_B. All entries are positive integers.

For t>=0 define

    D(t)=(t+z)(t+y)(t+yz+1)-(t+1)(t+x)(t+yz)
        =(y+z-x)t(t+yz+1)+yz(yz+1-x).

The first summand is nonnegative and the constant is strictly positive: yz+1>y+z>=x for integer y>z>1. Thus prod A < prod B, by applying D(jm)>0 separately for every j.

Every pole of either rational function is a root of unity. At 1 their difference has a pole of order 3L with positive leading coefficient

    c=1/prod A - 1/prod B > 0

in its expansion in powers of (1-q). No other root has order 3L for P_A because 1 is a part. No other root has that order for P_B because gcd(z,y,yz+1)=1: any common divisor of z and y divides yz but cannot divide yz+1. Hence all other poles have order <=3L-1. Partial fractions now give

    [q^n](P_A-P_B)=c*binom(n+3L-1,3L-1)+O(n^(3L-2)),

with a constant depending on this fixed parameter tuple. To justify the remainder, each term C/(1-q/rho)^s contributes C*rho^(-n)*binom(n+s-1,s-1), with |rho|=1 and s<=3L-1. A finite sum of these terms has the stated bound. The leading term is positive and of degree 3L-1, so every sufficiently large coefficient is positive.

This proves that, for each fixed admissible tuple, there are finitely many negative coefficients regardless of divisibility. It covers the divisible clause only, not the universal nondivisible positivity clause. It is a classical rational-function deduction, not a new full-scope solution. It supplies no explicit uniform threshold, no negative coefficient, and no acceptance claim.

Attempt to strengthen: replace each source part z+jm by z copies of 1 plus the shift, each y+jm similarly, and yz+1+jm by a yz-part and a unit. Weight preservation is easy but injectivity fails because original multiplicities can collapse into the same count of ones. Division with remainder by z or y may record some information in x-parts, but no inversion formulas have been found across all shifts. Andrews' termwise comparison from Theorem 4.2 covers x<=y, outside the hard literal region. Neither the failed injection nor eventual positivity is a sound Pi certificate plan for the missing clause.

## 325182: middle-generator normal form

Read source and journal Conjecture 5.1, its definition, and the adjacent parabolic decomposition. The full object is the generated submonoid of regressive order-preserving maps on [2N], not all centrally symmetric monotone maps. With mu_N omitted, mu_i=pi_i*pi_(2N-i) acts in two disjoint halves, and the word rearrangement in printed equations (5)–(6) separates them. The source already identifies this parabolic image with a double-Catalan construction and studies [4321]/[4231] fibers. Reusing that theorem alone does not count the full BNDPF_N.

First route: count pairs of Catalan maps from the two halves. This loses all trajectories crossing the N/N+1 boundary after applying mu_N; such crossings can occur again after other generators. A count of the parabolic part is therefore not an upper or lower equality proof for the full monoid.

Second route: the proposed sum suggests triples (I,J,D), I,J subsets of [N] of a common size j, and D a Catalan object of size j. To turn the count into a proof one needs (1) an invariant extracting I,J,D from every generated map, (2) a word constructing every triple, and (3) uniqueness. No extraction invariant invariant under all defining transformations and retaining middle-boundary data is proved here.

Third route: orient reductions on words so the middle generator appears in a controlled normal form. It is not enough to assume it appears once: idempotence only merges adjacent occurrences and does not commute it past its neighbors. A terminating, confluent reduction handling repeated returns to the middle is the exact missing lemma. The source's nearby parabolic fiber result already treats much of the easier normal-form mechanism. No enumeration was run and no claim beyond the source's N<=9 computations is made. Thesis 1108.4379 and later full citation bodies remain qualification gaps.
