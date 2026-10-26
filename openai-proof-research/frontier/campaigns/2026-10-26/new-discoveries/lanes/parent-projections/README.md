# Four-projection trace comparison: exploratory lane

Status: no proof, no counterexample, no discovery credit. Research date: 2026-10-26.

Target: MathDB 332493, Banica–Nechita, *Flat matrix models for quantum permutation groups*, arXiv:1602.04456v3, Conjecture 6.6 (printed p.20). The full primary PDF and text were read in `../parent-next-screen/sources/1602.04456.{pdf,txt}`. PDF SHA-256: `82ea37c2f43e0f2940ce190891306a08881d05149e98a0e743bbb48be5950fd1`.

Exact problem: orthogonal projections P,Q,R,S satisfy P perpendicular Q, R perpendicular S, Im(P) intersect Im(R)={0}, Im(Q) intersect Im(S)={0}, and the two rank-balance equalities rank(P)+rank(Q)=rank(R)+rank(S) and rank(P)+rank(R)=rank(Q)+rank(S). Thus rank(P)=rank(S)=a and rank(Q)=rank(R)=b. Define P',R' by symmetric whitening with (P+R)^(-1/2), and Q',S' with (Q+S)^(-1/2), using Moore–Penrose inverses. The target is

Tr(PR)+Tr(QS) >= Tr(P'Q')+Tr(R'S').

Source Proposition 6.7 already proves the case S=0. Do not count that case or a routine further small-rank case as a new discovery. Live solution records and later literature still require a fresh check before advancing a result.

`screen.py` uses a contraction parametrization. Take orthonormal frames U=[p,q] and V=[r,s] with ranks (a,b) and (b,a). Every contraction X=U*V can be realized in ambient dimension 2(a+b), with U the standard frame and V=[X; sqrt(I-X*X)]. Split X into blocks [[A,B],[C,D]]. Then the two within-pair Gram matrices are G1=[[I,A],[A*,I]] and G2=[[I,D],[D*,I]]. The cross Gram is H=[[0,B],[C*,0]], and the whitened cross Gram is H'=G1^(-1/2) H G2^(-1/2). The target compares ||A||F^2+||D||F^2 with the sum of squared Frobenius norms of the a-by-b and b-by-a diagonal blocks of H'.

The deterministic-seed numerical search used complex contractions, dimensions a+b from 2 to 10, up to three rank splits per dimension, eight restarts and 150 mutations each. Its 24 rank-split records are in `screen.json`. No positive RHS-minus-LHS was detected. The largest observed ratio was about 0.9045. This is only numerical evidence; it establishes neither a universal inequality nor absence of counterexamples.

For a=b=1 the script independently checks the closed formula for the whitened overlap, including its complex phase. A possible scalar optimization route was explored but has not been fully proved or formalized. It supplies no accepted result and should not be assumed as a lemma.

The broader goal remains a full source-faithful resolution or a genuine counterexample with exact arithmetic, full Lean, independent review, prior-art investigation, and a paper/proof packet. No external posting or contact occurred.
