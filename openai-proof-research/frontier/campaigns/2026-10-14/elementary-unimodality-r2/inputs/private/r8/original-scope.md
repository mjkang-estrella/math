# Frozen original target U — elementary unimodality

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT.
Frozen 2026-10-16 before proof work on U.

For EVERY integer n>=1 and EVERY weakly increasing integer function h:[n]->[n] satisfying i<=h(i)<=n, let G have edges {i,j} with i<j<=h(i), and M=|E(G)|. Define

    X_G(x;q)=sum_{f:[n]->positive integers, proper} q^{asc_G(f)} product_i x_{f(i)},
    asc_G(f)=#{i<j<=h(i): f(i)<f(j)}.

For EVERY partition lambda of n write c_(G,lambda)(q)=[e_lambda]X_G(x;q)=sum_(d=0)^M a_(lambda,d)q^d.

**U:** a_(lambda,d)=a_(lambda,M-d) for all 0<=d<=M, and

    a_(lambda,d+1)>=a_(lambda,d) for EVERY integer 0<=d<M/2.

All coefficients are integers and coefficientwise nonnegativity is already a stipulated pinned theorem. U asks for the full elementary unimodality assertion, over all graphs, partitions and degrees, including disconnected graphs and zero coefficients. It is the known remaining unimodality part of the Shareshian–Wachs conjecture; it is not advertised as an easy corollary. No log-concavity, special graph family, grouped partition sum, Schur-unimodality or dimension-unimodality substitute resolves U.

Potential route: compare the source incoming-coordinate sections with standard quantum theta functions and exploit acyclic Lefschetz positivity, paying every normalization/degeneracy/completion interface. A routine application, if sufficient, must be assessed as such rather than inflated. If the comparison or full inequalities remain unpaid, status is UNRESOLVED and no smaller theorem is nominated. No worldwide novelty claim, independent PASS or count change.
