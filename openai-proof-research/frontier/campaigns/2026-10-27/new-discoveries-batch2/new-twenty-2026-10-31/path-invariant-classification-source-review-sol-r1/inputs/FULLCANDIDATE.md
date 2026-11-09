# Full ordinary candidate: MathDB 339209

Status: ordinary proof proposed for adversarial review, NOT self-accepted. Zero credit. No formal execution. This is the full path algorithm claim, not just linear-system eigenspace invariance. Current public search3 did not identify a specific matching solution, but this is no novelty clearance. Final journal/correction and independent significance review remain unpaid.

## Source endpoint and dependencies
Original object originals/339209.jsonl. Acquired source sources/path.pdf SHA ac3959d30dbb35804c40679dbe6b3023b7e090253ec543fd8801c0e6be3c511e, identifies itself as arXiv1805.04144v2, 1 March2019. Definition2.2 p3: V=R^d, d positive; f_i=g(x_i)+sum_{j~i}h(x_j-x_i), g arbitrary odd and h arbitrary linear. Invariant means f(W) subset W for EVERY such f. Example6.3 pp26-28 and Conjecture6.4 p28 specify the algorithm. Basic words are G_s=(a1,...,as), E_(2s-1)=(a1,...,as,...,a1), s>=2, and O_(2s)=(a1,...,as,-as,...,-a1), O_(2s+1)=(a1,...,as,0,-as,...,-a1), plus O1=(0). A word S of length b is repeated as S,reverse(S),S,..., truncated only after an integer number k=n/b of whole blocks. Letters denote independent vectors of V. Claim: these and only these words give the invariant subspaces for P_n, n>=1.

## Reduction to signed polydiagonals, with independent justification
Take h=0. Arbitrary linear g on V acts simultaneously on every cell. Closure under all matrix units shows W=U tensor R^d for a scalar subspace U subset R^n: extract one coordinate by a matrix unit and insert it in any other coordinate. Choose a row echelon description of U in terms of independent free coordinates y_a. Every dependent coordinate is sum_a c_a y_a. Apply the odd map g(t)=t^3 coordinatewise. Invariance implies (sum c_a y_a)^3=sum c_a y_a^3 for all real free y_a. Coefficients of y_a^3 give c_a^3=c_a; coefficients of y_a^2 y_b give 3 c_a^2 c_b=0 for a!=b. Thus each coordinate is zero or plus/minus a single free coordinate. This reproduces the relevant content of source Proposition5.1 pp21-22 without assuming general graph classification. There are m independent parameters, and the coefficient row r_i belongs to {0,+e1,-e1,...,+em,-em}. The rows span R^m. Conversely this description is preserved by every odd g, including arbitrary odd g on vector V, because g(0)=0 and g(-v)=-g(v).

Take g=0,h=identity. W must be invariant under the path Laplacian L. Conversely, invariance under L together with signed-polydiagonal form implies invariance under every allowed linear h: h commutes with scalar coefficient combinations, and arbitrary odd g preserves the word. Therefore the desired condition is exactly signed-polydiagonal form plus L-invariance.

## Coefficient recurrence
Write R for the n by m matrix with rows r_i and full column rank. L-invariance means there is a unique m by m matrix Q with LR=RQ. No eigenvalue argument is needed. Introduce virtual rows r_0=r_1 and r_(n+1)=r_n. For every i=1,...,n,
 r_(i+1)=2 r_i-r_(i-1)-r_i Q.                 (R)
Rows are treated as row vectors; all formulas r_i Q have this orientation. If r_1=0, the endpoint equation forces r_2=0 and recurrence forces all rows zero: O1. Otherwise orient and rename the first parameter so r_1=e1.

While the sequence encounters new unsigned classes, orient each new class positively. Let q be the number of initial distinct classes, so r_i=e_i for 1<=i<=q. If all n rows are new, the word is G_n. Otherwise q<n, and r_(q+1) is either zero or epsilon e_j for j<=q. From (R) we already know
 e1 Q=e1-e2 (when q>=2),
 ei Q=2ei-e_(i-1)-e_(i+1) for 2<=i<q,
 eq Q=2eq-e_(q-1)-r_(q+1) (when q>=2).
For q=1 use e1 Q=e1-r2 directly.

## Exhaustion of the first return
For q>=2, the only possibilities are
 (A) r_(q+1)=eq;
 (B) r_(q+1)=e_(q-1);
 (C) r_(q+1)=-eq;
 (D) r_(q+1)=0.
Here is the missing exclusion calculation explicitly. For 2<=j<q, substitution into (R) gives, in the positive case r_(q+2)=e_(j-1)+e_(j+1)-eq. Unless j=q-1, the three basis indices are distinct, so this is neither zero nor a signed unit. When j=q-1 it reduces to e_(q-2) (q>=3). For j=1 the positive formula is e1+e2-eq, a forbidden row if q>2, and it is e1 for q=2, which is exactly case B. In the negative case 2<=j<q, the row is -e_(j-1)-e_(j+1)-eq; if indices merge, its coefficient has magnitude2, so it is always forbidden. For negative j=1 it is -e1-e2-eq, likewise forbidden. The case j=q is A or C and was not covered by the interior formulas.
These calculations require r_(q+2) to be in the row alphabet. If q+1=n, this row is the virtual endpoint r_(n+1)=r_n and is still in the alphabet, so no last-vertex exception is omitted. For q=1 the only choices r2=e1,-e1,0 give A,C,D respectively; there is no B. Recurrence gives the corresponding constant, signed double, or zero-center pattern. No search/enumeration is used.

## Propagation and final endpoint
In each remaining case Q is now completely specified on every encountered basis vector. Recurrence uniquely specifies all future rows. Direct substitution gives the following infinite words (the symbol rev means reversal):
 A: S=G_q, followed by rev(S),S,rev(S),...; basic length b=q.
 B: S=E_(2q-1), followed by rev(S),S,...; b=2q-1, q>=2.
 C: S=O_(2q), followed by rev(S),S,...; b=2q.
 D: S=O_(2q+1), followed by rev(S),S,...; b=2q+1.
For clarity, at the first turn in A the rows ...e_(q-1),eq,eq,e_(q-1)... have eq Q=eq-e_(q-1). In B the rows ...e_(q-1),eq,e_(q-1)... have eq Q=2eq-2e_(q-1). In C they are ...e_(q-1),eq,-eq,-e_(q-1)... with eq Q=3eq-e_(q-1). In D they are ...eq,0,-eq... with eq Q=2eq-e_(q-1), and the zero row obeys (R) because its neighbors sum to zero. At the left end use e1 Q=e1-e2, which produces repeated e1 or repeated -e1 at successive block boundaries. For q=1 substitute e1 Q=0,2e1,e1 in A,C,D. These formulas check every local row: internal steps are the stated second differences, turns are the four displayed expressions, and repeated endpoint rows give the left-end expression with its sign. Thus they establish the infinite recurrence, not merely an experimental pattern.
In these infinite words consecutive rows are equal precisely at positions i that are positive multiples of b (r_i=r_(i+1)). This follows from independence of the e_i: internal rows have distinct classes or opposite signs, zeros in D are isolated, the single peak in B is not doubled, and only block junctions double the outer endpoint letter. For A with q=1, every position is a junction and b=1. Consequently the right boundary r_(n+1)=r_n is equivalent to b dividing n. The obtained word is exactly the source algorithm with factorization n=bk.

If a first return never occurs before n, the word G_n has independent coordinates and is the whole phase space, already included. If it occurs, every future row is in the span of e1,...,eq by recurrence, so no previously unseen parameter may appear later. This closes the possibility of delayed new classes.

## Converse and scope
Every listed word has the just-checked quotient recurrence, including both endpoint conditions whenever b divides n. Hence LR=RQ and the subspace is L-invariant. Its signed word form preserves every odd g and every linear h as above; it is therefore D_(P_n,l)-invariant. This proves both directions for all positive n and all positive cell dimensions d, including all-zero and whole-space cases. Source ordering by reversed inclusion and figures are unnecessary to the universal proof. Example P6 agrees symbolically with the source's nine listed words; no mathematical program or finite verification was run.

## Limits and unpaid gates
This proof is a proposed ordinary argument and needs independent adversarial review, especially the tensor reduction and virtual-endpoint case. The literal MathDB record leaves its algorithm implicit; it is bound here to Example6.3 of acquired v2. Material Figure14 was subsequently rendered and visually inspected on source PDF page27 (figures/path-page27.png): nine subspaces, including the zero subspace, full space, reflected G3 and O6 words, E3, O2 and O3. Lattice arrows were inspected but are not used in the universal proof. Official arXiv metadata sources/path-metadata.html confirms v2 is the latest listed version, revised1March2019, and lists no journal reference. This does not establish absence of a later journal paper or correction; those have not been authenticated. Searches were bounded3calls9queries across the whole lane; no worldwide novelty claim. Registry root heads were acquired, exact matching registry theorem bodies were not audited. No specific competing path-completeness proof was identified in those bounded searches; absence is not evidence of novelty. Significance and accepted-family overlap require root/independent review. No formal endpoint exists. Do not credit or dispatch formal work from this lane.
