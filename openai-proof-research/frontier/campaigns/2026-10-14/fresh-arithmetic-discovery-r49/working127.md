# Two attempts at T127N49

## Credited input and exact restricted consequence

Source127, 01-introduction.tex thm:main, gives uniform-cube total influence <=8d sqrt(n), with arbitrary degree and zeros. The complete mathematical sections 01–06 were read (02 through line110, which covers its whole proof); its weighted grading and edge recovery are inputs, not new work. The source's sole manuscript and all non-PDF tracked files are retained. Source truth is stipulated.

Let t_i=min(p_i,1-p_i). For ANY numbers 0<=theta_i<=2t_i, independently declare coordinate i active with probability theta_i. If active set it to a fair independent sign; otherwise draw a fixed sign with plus probability (p_i-theta_i/2)/(1-theta_i). For theta_i=1, necessarily p_i=1/2, and the nonexistent inactive branch is omitted. Conditional on the active set and fixed signs, the resulting function is a uniform restriction of a degree<=d PTF. Its dimension is K, and influence <=8d sqrt(K), also if K<d by the trivial bound K<=d sqrt(K), and if K=0 by zero influence. Every other coordinate has its original marginal independently. Therefore

(R) sum_i theta_i I_i <=8d E sqrt(K)<=8d sqrt(sum_i theta_i).

This is a technical random-restriction transfer, not the target mechanism. Blais–O’Donnell–Wimmer, retained March2009 version, Theorem3.2 and Section4 (text541–665), already give the general two-independent-samples/selector transfer for product-noise sensitivity. The source's own Section06 gives the uniform degree-linear noise estimate. Arbitrary-product resampling noise bounds and learning transfers are consequently excluded as nominees.

## Route 1: active-coordinate mixtures and the square-root gap

For a single common bias p, choose theta_i=2min(p,1-p) in (R). This gives the target with constant 4sqrt(2). More generally dyadic bias grouping gives a logarithmic loss independent of the smallest atom: discard t_i<1/n at cost <=sqrt(n), since I_i<=1. Partition remaining t_i in dyadic bins [a,2a), including t_i=1/2 in the final bin. Each bin with k coordinates, theta_i=2a, satisfies sum_bin sqrt(p_i(1-p_i)) I_i <=8d sqrt(k). There are at most ceil(log_2 n)+2 bins, so Cauchy gives

sum_i sqrt(p_i(1-p_i)) I_i <=sqrt(n)+8d sqrt(n(ceil(log_2 n)+2)).

Conditioning/fixing all coordinates outside a bin preserves degree and the desired other-coordinate distribution. Thus the same bound follows directly from (R) with zeros outside that bin. n=1 can instead be treated directly. This is technical support and retains a growing loss; it does not prove T127N49.

The entire scalar family (R), together with 0<=I_i<=1, cannot remove this loss. Here is an explicit abstract numerical obstruction, NOT a PTF counterexample. For any m>=1 put k=4^m and n=mk. Have k coordinates at each level j=1,...,m. Set p_i=t_j=4^{-j}, M_j=k t_j=4^{m-j}, and a_i=M_j^{-1/2}. Regard a_i as abstract candidate influences. They lie in [0,1]. For arbitrary 0<=theta_i<=2t_j set x_j=sum_{i in level j}theta_i and S=sum_j x_j; then 0<=x_j<=2M_j. If S>0, split the geometric M_j according as M_j<=S or M_j>S. The first part contributes at most 2 sum_{M_j<=S}sqrt(M_j)<=4sqrt(S), and the second contributes at most S/sqrt(S)=sqrt(S). Consequently

sum_i theta_i a_i<=5sqrt(sum_i theta_i),

so every (R) inequality even with d=1 holds. Yet

sum_i sqrt(p_i(1-p_i)) a_i =sqrt(k) sum_j sqrt(1-4^{-j}) >=(sqrt(3)/2)m sqrt(k),

whose ratio to sqrt(n) is >=(sqrt(3)/2)sqrt(m). A further structural constraint on actual PTF influences is essential. No such vector is asserted realizable by a degree-one or any fixed-degree PTF.

For contrast, the full target DOES hold for degree one with constant 1/2: after coordinate sign flips a linear threshold is increasing, and with Y_i=(1_{X_i=+1}-p_i)/sqrt(p_i(1-p_i)), E[fY_i]=2sqrt(p_i(1-p_i)) I_i. Thus the sum equals (1/2)E[f sum_iY_i]<=sqrt(n)/2. This proves that the abstract obstruction specifically measures information lost by (R).

## Route 2: insert the product law in the source grading

The source builds K_r=sqrt(w)V_r in counting inner product; its grade dimensions are binomial, independent of w. For w=|P| and H=parity*sign(P), the low-block vanishing comes from sum parity*P*a*conjugate(b)=0 at total degree below n. Inserting a density mu into w changes this to sum mu*parity*P*a*conjugate(b), which is generally nonzero. Already n=1, P=1, w(+)=p, w(-)=1-p, and the unit grade-zero vector v=(sqrt(p),sqrt(1-p)) give <v,Hv>=2p-1. This violates the requisite grade-zero block vanishing whenever p!=1/2, even though the constant function has no influences. It is a failure of the proposed proof, not of the full target.

Using a mu-weighted Hilbert space and w=|P|/mu restores counting cancellation after conjugation, but its ordinary Hilbert–Schmidt trace still counts the 2^n point-basis vectors equally and recovers unweighted edges. Replacing that trace by a density-weighted state is not free: grade projection masses are no longer their dimensions, cyclic trace identities and the source's equal binomial coupling marginals are unavailable. Neither a weighted edge-recovery inequality nor a same-law low-variance grade coupling for that state has been derived. Source03,04,05 explicitly exhibit the exact missing identities.

## Status

The full target is unresolved. Two concrete routes were attempted: probabilistic mixture reduction and density-weighted operator grading. The first has the abstract sqrt(log n)-scale obstruction above; the second fails its exact low-block identity. No estimate closing either interface is claimed, and the special cases are not nominated.
