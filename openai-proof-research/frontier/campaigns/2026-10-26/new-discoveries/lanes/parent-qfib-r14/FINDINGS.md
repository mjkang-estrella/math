# q-Fibonomial n=4 — classical corollary, no discovery credit

General MathDB374706 remains unresolved here. Only the proposed next n=4 case
is disposed of; do NOT exclude the whole conjecture from further research.
No Lean/paper/acceptance is proposed for this familiar-theorem substitution.

For positive integers a,b, set
P(a,b;q)=[a]_q[b]_q[a+b]_q[a+2b]_q/([2]_q[3]_q).
Choose a rank-two crystallographic root system whose positive COROOTS, in its
simple-coroot basis, are (1,0),(0,1),(1,1),(1,2). For the dominant integral
weight lambda=(a-1)omega1+(b-1)omega2, Weyl principal specialization gives
q^(<lambda,rho-dual>)*chi_lambda(q^rho-dual)=P(a,b;q), with
2<lambda,rho-dual>=3a+4b-7=:D. The four numerator pairings are exactly
a,b,a+b,a+2b; the denominator pairings are1,1,2,3.

Restrict this finite-dimensional representation to the principal sl2. Complete
reducibility gives sl2 characters with nonnegative multiplicities. All highest
weights have the same parity as D, since every original weight differs from
lambda by an integral root combination and every simple root evaluates to2 on
2rho-dual. After the q^(D/2) shift, each summand is a contiguous interval
q^s(1+q+...+q^(D-2s)) centered at D/2. Their sum is symmetric and unimodal.
This is the standard principal-sl2 unimodality argument, not new machinery.

For n=4, put a=F_(m+1), b=F_(m+2). Fibonacci recurrence gives the four factors
a,b,a+b,a+2b, while [F4]!_q=[2]_q[3]_q. Thus the n=4 q-Fibonomial is exactly
P(a,b;q). This proves that case for every m>=0 by direct specialization.
The n=3 family similarly matches the type-A2 specialization. No assertion of
an earlier explicit q-Fibonomial n=4 publication is made or needed for exclusion:
it is an immediate corollary of the already-established representation theorem.

Primary theorem actually read: John R. Stembridge, Computational Aspects of Root
Systems, Coxeter Groups, and Weyl Characters (2001), Theorem7.4/Corollary7.5,
printedpp31-32, including the principal-sl2 weight-space interpretation. Both
pages rendered/read. Author-hosted PDF:
https://websites.umich.edu/~jrs/papers/carswc.pdf
The actual2026 q-Fibonomial source Connelly et al2605.12822v1, Conj1.1p1 and
future-work pp13-14 were also rendered/read; it only claims n<=3. Theorem use
above is an application beyond that source's stated coverage, not a new theorem.

check_b2.py exact checks2500 arbitrary positive pairs and11 Fibonacci identities,
including dimension limit6P(1)=a*b*(a+b)*(a+2b). These checks corroborate the
identification, not the universal representation proof. No general m,n theorem
or new q-FiboCatalan positivity result follows from this n=4 identification.
