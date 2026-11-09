# MathDB 333569: ordinary proof candidate, not an accepted Lean solution

The exact target is Petersen, arXiv:1607.02425, Conjecture 4.6.8, and the earlier Petersen–Wilson arXiv:1512.01143, Conjecture 6.3. The latter paper still states the question, and its Proposition 5.10 and proof supply the Markov entropy-series bridge. Both full PDFs and extracted texts are cached with dated hashes. This is an existence theorem, not a claim of uniqueness, an exact numerical optimizer, or a global maximum. No discovery-credit or worldwide-priority claim is made. Formalization and bounded registry/body comparisons remain incomplete.

Write h(x)=-x log x-(1-x)log(1-x), extended continuously by zero at 0 and 1. For 0<l<1 and |t|<1, let pi=((1+t)/2,(1-t)/2), and let

P(l,t) = [[1-(1-l)(1-t)/2, (1-l)(1-t)/2],
          [(1-l)(1+t)/2, 1-(1-l)(1+t)/2]].

All four entries are strictly positive, pi P=pi, and P has other eigenvalue l. This parameterization is a smooth coordinate chart around every symmetric matrix with 0<l<1: for diagonal entries u,v, l=u+v-1 and t=(u-v)/(2-u-v). It therefore suffices to establish a local maximum in these two coordinates. Its stationary Markov measure gives positive probability to every cylinder. Cylinder probabilities depend continuously on these coordinates, and conversely u,v are ratios of positive length-two and length-one cylinder probabilities; thus the parameter and measure topologies agree locally.

Put x_r=(1-r)/2 and

H(r,t) = (1+t)/2 h(x_r(1-t)) + (1-t)/2 h(x_r(1+t)).

Induction gives P(l,t)^i=P(l^i,t). Stationarity gives H(X_0|X_i)=H(X_i|X_0)=H(l^i,t). The entropy rate is H(l,t). By the proof of Proposition 5.10, intricacy equals

F(l,t) = sum_{i>=1} 2^{-i} H(l^i,t) - H(l,t).

Here is also a direct bridge from the literal finite-subset definition. For selected times s_1<...<s_k in {0,...,N-1}, the Markov chain rule gives H(X_S)=H(pi)+sum_{j=2}^k H(l^{s_j-s_{j-1}},t). The empty set contributes zero. Averaging over independent fair inclusion of each time, the expected number of consecutive selected pairs at gap i is (N-i)2^{-(i+1)}. Consequently

2 Asc_N = 2(1-2^{-N})H(pi)/N + sum_{1<=i<N} (1-i/N)2^{-i} H(l^i,t).

The block entropy divided by N tends to H(l,t), and bounded convergence, using 0<=H<=log 2, proves the displayed expression for F. This argument proves the bridge for the literal source weights, rather than assuming it as an axiom.

On the symmetric line put f(l)=F(l,0). It extends continuously to [0,1]. Indeed the series is uniformly convergent since each summand is bounded by 2^{-i} log 2. At l=0 every entropy in the weighted average is log 2, so f(0)=0; at l=1 every term is zero, so f(1)=0. For 0<l<1, h((1-l^i)/2)>=h((1-l)/2), with strict inequality for i=2. Since the weights sum to 1, f(l)>0. The extreme value theorem gives a global maximum at some l_0 strictly between 0 and 1.

The missing step in a diagonal-only argument is transverse stability. The following exact calculation supplies it. H is even in t. Its coefficient of t^2 at t=0 is

c(r) = -x_r log((1-x_r)/x_r) - x_r/(2(1-x_r))
     = -(1-r)/2 log((1+r)/(1-r)) - (1-r)/(2(1+r)).

Differentiation gives

c'(r) = (1/2)log((1+r)/(1-r)) - r/(1+r)^2.

The right side vanishes at r=0, and its derivative is 4r/((1-r)(1+r)^3)>0 for 0<r<1. Thus c is strictly increasing on [0,1). It follows that

F_tt(l,0)=2[sum_{i>=1}2^{-i}c(l^i)-c(l)]<0

for every 0<l<1: all differences c(l^i)-c(l) are nonpositive, with i=2 strictly negative.

For completeness, this differentiation of the infinite sum is legitimate uniformly near (l_0,0). Choose 0<a<l_0<b<1 and 0<delta<1. For l in [a,b], |t|<=delta, and every i>=1, both arguments of h in H(l^i,t) lie in the compact interval [(1-b)(1-delta)/2,(1+delta)/2] inside (0,1). The first two t derivatives of H are therefore bounded independently of i,l,t. The geometric majorant proves uniform convergence of the series and both t-derivative series. In particular F_tt is jointly continuous there.

Since F_tt(l_0,0)<0, shrink to a rectangle about (l_0,0) on which F_tt<0. Evenness gives F_t(l,0)=0 throughout this rectangle. Integrating F_tt twice shows F(l,t)<=F(l,0) there, with strict inequality when t is nonzero. Finally F(l,0)<=F(l_0,0) by the choice of l_0. Hence (l_0,0) is a local maximum of F in the full two-dimensional parameter space. The corresponding stationary one-step Markov measure is fully supported and is a local maximum of the literal source intricacy functional. This proves the ordinary mathematical assertion.

## Exact formalization gap and next lemmas

No kernel-checked proof of this endpoint is present. A full certificate must prove, not assume: (1) the finite-cylinder entropy chain rule and finite-subset averaging identity above; (2) the limiting series identity and summability; (3) uniform differentiability in t; (4) c monotonicity; (5) compact diagonal maximization and transverse local maximality; and (6) the correspondence with stationary Markov measures and the local topology on those measures. Merely proving an abstract Hessian lemma or defining F is insufficient. The pinned mathlib contains trajectory-kernel infrastructure, but no preexisting intricacy bridge was identified in the limited local search. An exact finite-cylinder assertion is recorded in Target333569.lean; it is only definitions, not a proof or semantic-bridge certificate.

The bounded prior-art search found earlier statements of the same conjecture, not a resolution. This is not novelty clearance: the accessible current OpenAI head receipt is only a head receipt; MathDB and Palomar remain denied under inherited access limits; later primary citing bodies and current repository full-body comparisons remain to be completed. The derivation may still be deemed a routine entropy-series consequence under the campaign's significance standard. Independent adjudication is required before investing in a long formalization.
