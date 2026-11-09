# Complete elementary replacement for the arithmetic dependency of MathDB 359585

Status: ordinary handwritten proof, not a formal certificate. Credit 0. No numerical experiment, mathematical program, Lean execution, CAS, solver, or child delegation. This is a weaker sufficient replacement for an older published arithmetic input, not a claim that this number-theoretic estimate is new to the literature. The graph construction remains the root-qualified candidate. No new novelty or acceptance adjudication is made here.

## Statement

For each integer N >= 2 let L be its binary bitlength, characterized by 2^(L-1) <= N < 2^L. There exists an integer a with 1 <= a < N and gcd(a,N)=1 such that every quotient in ordinary Euclidean division of (N,a) is < 4L^2, the number of divisions is < 2L, and their sum is < 8L^3. Consequently the positive subtractive Euclidean word from (1,1) to (N,a) has length <= 8L^3-1. These quantifiers concern the given N itself, for every N, including composite N and primes. No averaging over denominators or denominator change occurs.

We prove everything quantitative below. Only elementary integer arithmetic (division with remainder and induction) and finite sets are used. Rationals in cardinal inequalities avoid floor-rounding ambiguities; there are no asymptotic estimates or analytic constants.

## 1. A lower bound on units, with proof

Let p_1 < ... < p_k be the distinct primes dividing N. Every integer greater than 1 has a prime divisor: choose its least divisor greater than 1; if that divisor were composite it would have a smaller such divisor. Repeated division and induction gives a prime factorization. Euclid's lemma follows from Bezout: if gcd(u,v)=1, division with remainder preserves the gcd and back-substitution expresses 1 as xu+yv; multiplication shows u|vw implies u|w. This also shows that products of distinct prime divisors divide N. No estimate about the distribution of primes is used.

Let U_N={a:0<=a<N, gcd(a,N)=1}, with cardinal phi(N). An a is in U_N precisely when none of the p_i divides it. In one direction a shared prime divisor forbids gcd 1. In the other a common divisor >1 has a prime divisor by the preceding least-divisor argument. For each subset S of the prime divisors, exactly N/prod(S) residues in [0,N) are divisible by every member of S: their common multiples are precisely multiples of prod(S), which divides N; these are 0,prod(S),...,N-prod(S). The assertion about common multiples follows by repeated Euclid's lemma.

Expanding the product of indicators prod_i(1-1_{p_i|a}) and summing over residues gives, term by term,

  phi(N) = N prod_{i=1}^k (1-1/p_i).

This is a proof of the product formula, including its gcd and finite-counting content, rather than an invocation of a totient asymptotic. Since increasing distinct integers at least 2 have p_i >= i+1,

  N/phi(N) = prod p_i/(p_i-1)
           <= prod (i+1)/i = k+1.

Indeed p_i/(p_i-1)=1+1/(p_i-1)<=1+1/i, and the last product telescopes. Also 2^k <= prod p_i <= N < 2^L; hence k<L and k+1<=L. We have proved

  phi(N) >= N/L > 0.

For N>=2 the residue 0 is not a unit, because gcd(0,N)=N. Thus all these units lie in [1,N-1].

## 2. Exact congruence count and the cancellation that avoids divisor losses

Fix 1<=q<N and put g=gcd(q,N), q=gq', N=gn'. If aq == epsilon*r (mod N), where epsilon is +1 or -1 and r>0, then g|r. If g does not divide r there is no solution. If r=gt, the congruence is equivalent to a q' == epsilon*t (mod n'). Now gcd(q',n')=1: a larger common divisor would make a common divisor of q,N exceeding their gcd. Bezout supplies an inverse of q' modulo n', so there is exactly one residue class of a modulo n' solving this congruence. The inverse follows by reducing xq'+yn'=1 modulo n'; uniqueness follows by the same identity. That class has exactly g representatives in [0,N), namely b+j n', 0<=j<g, for its unique b in [0,n'). This includes the case n'=1.

For any positive integer K, count pairs (a,r) satisfying 0<=a<N, r>=1, Kqr<=N and the congruence for this fixed q and fixed sign. The allowed nonzero r divisible by g are g,2g,...,g floor(N/(Kqg)). Each has exactly g choices of a. Therefore the exact pair count is

  g floor(N/(Kqg)) <= N/(Kq).

There is NO additive rounding error and NO remaining factor g. This is the essential point. The zero remainder must be excluded: allowing it would invalidate this useful bound.

Let B_K be the residues a in [0,N) admitting at least one witness consisting of q in [1,N-1], r>=1, a sign epsilon, Kqr<=N and aq == epsilon*r (mod N). The union bound, with repetitions allowed, gives

  |B_K| <= (2N/K) sum_{q=1}^{N-1} 1/q <= 2NL/K.

For completeness, the last sum bound is finite and elementary. Partition the q into the L blocks [2^j,2^(j+1)), j=0,...,L-1, omitting q>=N. Each block has at most 2^j terms and each term is at most 1/2^j; its sum is at most 1. Since N<2^L these blocks cover [1,N-1]. Hence the sum is at most L.

Take K=4L^2. Then |B_K|<=N/(2L)<N/L<=phi(N). If every unit belonged to B_K its cardinality would be at least phi(N), a contradiction. Thus some a in U_N lies outside B_K. This establishes coprimality before any Euclidean step and uses no condition about typical denominators.

## 3. Every large Euclidean quotient supplies a counted nonzero witness

For that a, apply division with remainder, starting r_0=N, r_1=a, and continuing

  r_{i-1}=Q_i r_i+r_{i+1}, 0<=r_{i+1}<r_i,

as long as r_i>0. Strict descent of positive integers proves termination. Write r_s>0 for the last positive remainder, so r_{s+1}=0. The common divisors of x,y are exactly those of y,x-Qy, so gcd invariance and gcd(N,a)=1 give r_s=1. Before termination r_{i-1}>r_i>=1 and Q_i>=1; at the last step Q_s=r_{s-1}>=2. This also covers a=1 and s=1.

Set q_0=0,q_1=1 and q_{i+1}=Q_i q_i+q_{i-1}. Induction gives q_i>=1 for i>=1. Two further induction invariants are

  N=q_i r_{i-1}+q_{i-1} r_i,
  r_i == (-1)^(i-1) a q_i (mod N),  i>=1.

The first begins N=1*N+0*a, and its induction step is the identity

 (Q_i q_i+q_{i-1})r_i+q_i(r_{i-1}-Q_i r_i)
   =q_i r_{i-1}+q_{i-1}r_i.

For the signed congruence the i=1 case is a==a, and i=2 follows from r_2=N-Q_1 a and q_2=Q_1. Subsequently subtracting Q_i times the i-th signed congruence from the (i-1)-st gives the (i+1)-st, since the two consecutive signs are opposite and q_{i+1}=Q_i q_i+q_{i-1}. Equivalently start at i=0 with r_0==0 and q_0=0; this avoids any negative exponent. Signs are just alternating plus/minus, not analytic objects.

At every division r_{i-1}>=2 and q_{i-1}r_i>=0, so the first invariant gives q_i<=N/2<N. If Q_i>=K, that same identity gives

  N >= q_i r_{i-1} >= Q_i q_i r_i >= K q_i r_i.

Thus q=q_i, r=r_i>=1 and the appropriate sign are a witness putting a in B_K, contradiction. Hence every Q_i<K. The witness is never the terminal zero remainder. In particular this controls the often troublesome FINAL quotient as well as the first one. No continued fraction theorem, cylinder measure, equidistribution, or convergence estimate has been imported.

## 4. Number of divisions and subtraction length

Whenever r_i,r_{i+1},r_{i+2} are positive, r_{i+2}<r_i/2. If r_{i+1}<=r_i/2 this follows from r_{i+2}<r_{i+1}; otherwise floor(r_i/r_{i+1})=1 and r_{i+2}=r_i-r_{i+1}<r_i/2. Thus if s>=2L, repeated application would yield 1<=r_{2L}<N/2^L<1, impossible. Therefore s<2L. Since all Q_i<K=4L^2,

  S=sum_{i=1}^s Q_i < (2L)(4L^2)=8L^3.

The positive subtraction process agrees with these division blocks, up to ordering the two coordinates: in a nonfinal division, Q_i subtractions of the smaller from the larger leave the pair (r_i,r_{i+1}), with orientation alternating. In the final division the pair is (Q_s,1); exactly Q_s-1 subtractions reach (1,1), avoiding zero. Therefore the total is exactly S-1 and in particular <=8L^3-1. Reversing these subtractions gives a word in X:(u,t)->(u+t,t) and Y:(u,t)->(u,u+t) from (1,1) to the ORDERED pair (N,a). Record which coordinate was subtracted, so no free state-swapping operation is assumed. Gcd is preserved because a divisor divides x,y iff it divides x-y,y (or x,y-x). Positivity is preserved until equality. All cases, including N=2, were covered without a finite computational check.

## 5. Actual bicircular graphs and explicit encoding bound

This section spells out how the proved arithmetic lemma connects to the already independently reviewed ordinary graph construction; it does not replace graph states by abstract arithmetic.

Use finite undirected edge-indexed graphs allowing loops. A pseudoforest is a spanning edge subset with at most one cycle per component. Let G be connected and contain a cycle. U counts the subsets all of whose components are unicyclic. T counts those whose root component is a tree and every other component is unicyclic. A tree has v-1 edges; a unicyclic connected pseudoforest has v edges, including the one-vertex single-loop case.

The bases of B(G), whose independent sets are pseudoforests, are exactly the U subsets. Each U subset has |V| edges, while any independent subset has at most |V| edges, so it is maximal. Conversely a tree component in an independent subset can be augmented: if it is not all vertices, an ambient connecting edge to another component exists and merges a tree with a tree or a unicyclic component without creating two cycles. If it contains all vertices, it is a spanning tree; an unused ambient edge exists since G has a cycle, and adding it creates exactly one cycle. Thus a maximal independent subset has no tree components. This verifies maximality, including isolated vertices and absent bridges.

Seed: one vertex with one labeled loop gives exactly one U state and one T state. X adds a new labeled loop at the root. New U states omitting it are old U states, and those containing it are old T states by deleting/adding the new loop; a root already unicyclic cannot take a second cycle. New T states must omit it and are old T states. These inverse bijections give (U,T)->(U+T,T).

Y adds one new vertex s and one edge from the old root to s, then takes s as root. Every new U state uses that edge, and deleting the leaf gives precisely an old U state. New T states omitting the edge isolate s and correspond precisely to old U states; those containing it correspond precisely to old T states by leaf deletion. The cases are disjoint with explicit inverses, giving (U,T)->(U,U+T). Graph connectedness and the seed cycle persist. X adds one edge; Y adds one vertex and one edge. No edges are identified, including loops at the same vertex.

Interpreting the word of Section 4 therefore gives b(B(G))=U(G)=N. Its size s_G=|V|+|E| is at most 2+2(S-1)=2S<=16L^3. For N=1 use the seed, and L=1, so the same bound holds. We make no simplicity or polynomial-time construction claim.

Here is a deliberately loose but fully explicit polynomial bit encoding. Number v vertices 0,...,v-1 and order the m edges by creation. Encode v and m as unary strings 1^v0 and 1^m0. Encode each of the two endpoints of each edge in exactly v binary bits; v>=1 and every vertex index is <v<=2^v, the latter inequality following by induction from 1<=2 and v+1<=2v for v>=1. Equal endpoints encode loops; repeated pairs are separate edges by position. The decoder knows the endpoint width and list length from the two unary headers. If desired, multiple syntactic representations may encode one undirected graph; a unique canonical representation is unnecessary. The total length is

  v+m+2+2mv <= s_G+2+2s_G^2 <= 4s_G^2 <= 1024L^6,

where s_G>=2. Thus every positive N has a genuine finite bicircular presentation with exactly N bases and an explicit bitlength bound 1024*(bitlength N)^6. Unary headers are intentional: their cost remains polynomial in bitlength N and removes any hidden logarithm estimate. Use sharper headers if desired; no improvement is needed.

## 6. Dependence, limits, and formalization cost

Goal A is closed at the ordinary-proof level. There is no residual unproved arithmetic lemma in this manuscript. ABH Corollary 2, its analytic proof, and any canonical-CF machinery are entirely absent from the proof dependency chain. No all-N bounded-constant quotient conjecture is claimed: our quotient bound grows as 4L^2. Averaging is over residues of the FIXED N; the selected residue is explicitly a unit. This is not an average bound on the full untruncated quotient sum, which may be much larger because of exceptional numerators.

The inherited source qualification is not broadened by this arithmetic work. No live prior-art/source-body claims were made; no HTTP requests were needed. Existing source review and root qualification are read as task context; they are not presented as new source verification. The weaker arithmetic lemma should be treated as a proved elementary input, not a separate credited discovery. Full acceptance still needs the actual bicircular matroid formalization, independent statement review, transitive axiom audit, and strict extracted replay. No Pi execution or dispatch is authorized by this file.

A concrete prospective implementation order (NOT executed):

A1. Define a finite set of witnesses (q,r,sign,a), with 1<=q<N, 1<=r<=N and K*q*r<=N. Prove the fixed-(q,r,sign) fiber cardinal is either 0 or gcd(q,N), via Bezout and residue representatives. Then sum first over the allowed positive multiples of gcd, proving g*floor(N/(Kqg))<=N/(Kq) over rationals. Counting (q,a) with a merely existential would also work, but the pair count is simpler to upper-bound.

A2. Prove the dyadic block reciprocal-sum bound by partitioning [1,N) into L intervals. Prove phi(N)*L>=N using the read Euler product theorem, order the finite prime-factor set and prove p_i>=i+1. Its cardinal k satisfies 2^k<=N. These ordering/product and dyadic lemmas are new formal work; no exact API for them was verified. Combine inequalities to choose a unit outside the witness projection.

A3. Implement a division trace by well-founded descent of the current smaller coordinate. Carry the q recurrence, the two exact invariants in Section 3, positivity, and a signed residue invariant. Define division count and quotient sum on that trace. Prove the two-step-halving lemma and s<2L. Large quotient yields a witness, so S<8L^3. This route bypasses canonical CF definitions and the need to identify a CF quotient-sum library theorem.

A4. Convert the trace to a coordinate-oriented subtraction word and prove length S-1, with the final positive pair (1,1). Alternatively prove the weaker <=S bound if that simplifies recursion, adjusting graph constants to 18L^3 and 1296L^6. The sharper constants in this proof use the exact final minus-one.

G1. Independently formalize finite edge-indexed looped graphs and the actual bicircular matroid: independence=pseudoforest must be proved or derived from an actual transversal matroid via incident-edge matchability. No claim that such an endpoint was found in mathlib. Prove the maximality bridge and explicit finite state equivalences for X/Y above. This is substantial graph/matroid work that the arithmetic proof does not pay automatically.

G2. Interpret words as graph constructions with size invariant, prove endpoint-list decoder/length bound, then combine all positive N, including the N=1 seed. No arithmetic, semantic, or encoding assumption may remain in the final theorem. Audit only after implementation with the authorized model, and require independent scope review and strict extracted rebuild. No estimate in hours or promise of a mechanical port is justified here.

Pinned text inspected, at the task-specified mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612 (revision supplied by task, no git verification performed):

* Mathlib/Data/Nat/Totient.lean lines 35-62: Nat.totient definition; Nat.totient_eq_card_coprime; Nat.totient_eq_card_lt_and_coprime, including its equivalence body.
* Same file lines 283-332: Nat.totient_eq_prod_factorization; Nat.totient_mul_prod_primeFactors; Nat.totient_eq_div_primeFactors_mul; Nat.totient_eq_mul_prod_factors with statement `(phi n : Q) = n * prod p in n.primeFactors, (1 - (p : Q)^(-1))`, and all their displayed bodies. This directly supports A2's Euler product input, but is not itself the unit lower bound or small-word theorem.
* Mathlib/Data/Nat/Size.lean lines 25-103: Nat.lt_size_self, Nat.size_le, Nat.lt_size, Nat.size_pos, including proofs. Nat.lt_size_self gives N<2^Nat.size N; Nat.lt_size gives k<Nat.size N iff 2^k<=N. These match the required bitlength conventions.
* Mathlib/Data/Nat/GCD/Basic.lean lines 180-199: Nat.coprime_sub_self_left/right and Nat.coprime_self_sub_left/right, with bodies reducing to gcd identities. They match subtraction coprimality in A4.

Targeted rg queries in these three files are separately recorded in the read inventory. No full CF/Euclid/congruence counting existence theorem was searched for or claimed present. No transitive source-body audit or formal verification of these declarations occurred; only literal text was read. All uninspected API in A1/A3/G1 remains implementation work, not assumed available.
