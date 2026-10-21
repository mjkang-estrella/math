# Independent correctness derivation (working record)

Target is exactly the supplied frozen scope, authenticated SHA256 b5c7b51d352e250df511fae5d3456ccbaa2756180111020b3108415c12a7d813; proof SHA256 f522cf05688e557aa7934946ee79564ee55238f0057423135a58c4d9abee451a. No grade inherited from the author. Only correctness is assessed.

## Incidence and feasibility: author lines 12,20-67,105-125

Write h=N/q, x=|X| and z=|Z|. The blocks of a fixed partition are distinguishable by their vertex sets even though their collection is unordered. Hence its column incidence degree is D=h!/product(t_alpha!) times product multinomial(q;alpha)^t_alpha. Its row incidence degree is a=xD/z by transitivity and double counting. Thus p=a/x=D/z is positive. A direct allocation of vertices into alpha slots for every prescribed block uses exactly s_u vertices of each color, and proves feasibility for every admissible table. No further divisibility or positivity assumption is necessary.

The ordinary rectangular matrix of T is I/a, while its uniform-inner-product adjoint is I^transpose/D. Consequently TT* has ordinary entries |row(z) intersect row(z')|/(aD), equivalently b/(z p^2). The ordinary qth trace is z^(-q) sum over cyclic tuples of product(b/p^2). This is not a dimension-normalized trace. Equality with the trace on X follows from equality of nonzero singular values, including multiplicities.

For a joint table on pair colors, permutation invariance of the ordered q slots and the collapsed composition law t/h imply each tuple marginal is exactly P_t. The coordinate pair marginal is sum_beta beta_(u,v)v_beta/(qh)=R_(u,v), not a product of its marginals. Joint tables partition the event of having the target table at both colorings. Their count is at most (h+1)^m(q,ell^2). The maximizing compatible joint table may vary by edge; no common block law is needed.

## Boundary constants and entropy cancellation: author lines 39-54,73-99,115-136

For j>=1, monotonic integral bounds give 1<=R_j<=1+log(j) (j=1 included); the proof's weaker 0<=R_j<=1+log(j+1) is valid, and R_0=0. With U=1+log(N+1), the exact log(D/Z) remainder is R_h-sum_beta R_v-R_N+sum_j R_n. Its negative part is at most (m(q,r)+1)U and positive part at most (r+1)U. Zero entries simply contribute zero remainders.

For vertex type Gamma, log of its multiplicity divided by z^q has remainder (1-q)R_N-sum_gamma R_(NGamma)+q sum_u R_su. This is <=q ell U, hence certainly <=(1+q ell)U as stated. No missing ell^q error is required here because the entire negative sum may be dropped. Summing possible joint block tables costs at most m(q,ell^2)U. Each edge then costs [m(q,ell^2)+ell^2+1+2(m(q,ell)+1)]U after dividing by p^2.

For a finite probability law, nonnegative relative entropy follows from log x<=x-1 on its positive support. Conditional mutual information is an average of such quantities, so conditioning reduces entropy. The mutual-information chain rule gives I(A^q;B^q)>=I(A_1;B_1) separately for every edge law Q_i. Rooting each of the q trees made by deleting one cycle edge gives TC(Gamma)>=sum_tree I_i. Averaging gives TC>=(q-1)/q sum I_i. Hence -TC+sum I_i-(1/q)sum J_i<=0. This is a full finite-alphabet derivation, including zero probabilities, and assumes no compatibility among different Q_i beyond their individually verified marginals.

The coefficient of N in the trace type sum is H(Gamma)+qH(pi)-sum H(R_i)+(1/q)sum H(Q_i)-2H(P), exactly the preceding nonpositive quantity. There are at most (N+1)^(ell^q) vertex types. With C0=1+q ell+q[m(q,ell^2)+ell^2+1]+2q[m(q,ell)+1], the trace is <=exp(C0)(N+1)^(C0+ell^q)<=exp(C)(N+1)^C. This checks the unchanged explicit C for every admissible N, q>=3 and ell>=1.

## Representation and compression: author lines 140-186

For A of d fixed vertices, two q-block partitions are in the same S_(N-d) orbit iff they induce the same equivalence relation on A. Each class occupies one block with q-|class| free vertices; align these free vertices class by class, then biject the untouched full blocks. This constructs the required permutation. Products of b_ij and 1-b_ij are exact orbit indicators. Upon expansion every nonzero product uses disjoint blocks containing at least two A vertices, so has at most floor(d/2) distinct full-block factors. Thus all G-fixed vectors lie in P_d.

If lambda_1>=N-d, the one-row diagram (N-d) is a subdiagram. A sequence of removable corners outside it gives a restriction path and a trivial G subrepresentation. Applied to any irreducible copy in P_d-perp this contradicts its fixed-vector exclusion. Likewise lambda'_1>=N-d would give a sign G subrepresentation. Since h>d, at least one of the h blocks avoids A; swapping two of its vertices fixes the partition and changes any sign function's value to its negative. Such a function vanishes pointwise. This excludes the column case without multiplicity-free assumptions.

Both row and column lengths are therefore <N-d. Their product is >=N; transpose to make the first row b>=sqrt(N)>=2d. There are more than d boxes below it. Delete lower corners to retain exactly d lower boxes; their column indices are <=d. Fill the first d top-row boxes with 1,...,d; choose d of the b labels d+1,...,b+d for the lower diagram in fixed standard order; place the remaining b-d in increasing top-row order. All column inequalities hold because each top entry over a lower box is <=d. A fixed extension chain gives binomial(b,d) distinct standard tableaux of lambda. Since each of the d falling factors is >=b/2, dim lambda>=N^(d/2)/(2^d d!). Primary branching/tableau reading is recorded separately.

A=T*T and Q=I-Pi_d commute with the group but need not commute with each other. B=QAQ restricted to QH is PSD and equivariant. Courant-Fischer on a smaller family of subspaces gives lambda_j(B)<=lambda_j(A). Hence tr(B^q)<=tr(A^q), without incorrectly asserting (QAQ)^q=QA^qQ. The top eigenspace is invariant and has dimension at least c_d N^(d/2). Also ||B||=||TQ||^2. Thus c_d N^(d/2)||TQ||^(2q)<=exp(C)(N+1)^C.

The exact d=ceil(2C+4qK+2) gives d/2>=C+2qK+1; N>=4d^2 and N>=qd+1 justify all dimension hypotheses. N>=exp(C)2^(C+d)d! absorbs the remaining factor after (N+1)^C<=2^C N^C. Therefore ||TQ||^(2q)<=N^(-2qK). The zero complement and B=0 cases are automatic. No change to d or N0 is needed.

## Simultaneous polynomial: author lines 190-201

For fixed z and any set E of disjoint specified q-blocks, m_alpha counts blocks by their composition and a_u counts their distinct vertices. Apply an independent uniform permutation in every color cell to a partition of table t. The table fiber is one orbit, so the resulting law is exactly uniform. Inverse images of the a_u fixed vertices are uniform ordered injections, with denominator product(s_u)_(a_u). To realize E, select ordered distinct blocks of each type in (t_alpha)_(m_alpha) ways and assign the specified color-u vertices within each block in alpha_u! ways. The favorable assignments are disjoint and exhaustive. The probability is exactly formula (7.1), of degree |E| and with positive denominator independent of t.

Repeated generators are idempotent; overlapping distinct specified blocks give zero. An expansion of Pi_d f in the fixed finite generating family exists over the reals and is chosen before varying t. Coefficients do not depend on t because X, its uniform inner product and Pi_d do not depend on t. This proves the single polynomial for every real f and every integer d>=0, including d>N/q and d=0. For t_alpha<m_alpha the falling factorial vanishes; no division by a table entry occurs.

## Diagnostic logic

In the balanced monochromatic example D=binomial(h,h/2), and TT* has diagonal 1/D, so its nonnegative matrix has tr((TT*)^p)>=|Z|/D^p from the constant cyclic paths alone. The exponent (1-p/q)N log 2+O_q(log N) follows from the same factorial remainder estimates. This explains the second-moment obstruction for q>=3 but supplies no premise for the uniform qth-moment proof. Finite diagnostics will be documented separately and cannot substitute for these deductions.
