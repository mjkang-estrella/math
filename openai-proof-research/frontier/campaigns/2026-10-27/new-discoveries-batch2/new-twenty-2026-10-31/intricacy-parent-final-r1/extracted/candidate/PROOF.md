# A fully supported local intricacy maximum on the two-shift

Formal proof candidate for MathDB333569. Independent formal/fidelity review, paper adjudication, bounded prior-art completion and root acceptance remain pending. This manuscript records the complete mathematical argument certified by the accompanying Lean sources; it makes no priority claim.

Let h(x) = -x log x -(1-x) log(1-x), with the usual continuous endpoint extension. For 0<l<1 and |t|<1 set pi=((1+t)/2,(1-t)/2) and

P(l,t) = [[1-(1-l)(1-t)/2, (1-l)(1-t)/2], [(1-l)(1+t)/2, 1-(1-l)(1+t)/2]].

The entries are strictly positive and pi P=pi. Writing J for the matrix with rows pi gives P=J+l(I-J), J²=J, and hence P^i=P(l^i,t). The accompanying construction gives an actual countably additive probability law on {0,1}^Z with these cylinder probabilities. Every integer shift preserves it and every nonempty open set has positive mass.

For selected times s0<...<sd the cylinder probability is pi(a0) times the product over j of P(l^(s[j+1]-s[j]),t)[a[j],a[j+1]]. To prove this without a Markov assumption, first partition an arbitrary finite past event by full block atoms. The proved contiguous-cylinder identity factors its next symbol. Partition again by each intermediate symbol and induct on the gap; matrix composition contracts the resulting finite sum. Induction on the selected list gives the displayed product.

Let H(r,t) be the stationary conditional entropy of P(r,t):

H(r,t)=(1+t)/2 h((1-r)(1-t)/2)+(1-t)/2 h((1-r)(1+t)/2).

The finite Shannon chain rule follows directly from log(xy)=log x+log y and row normalization. Each endpoint retains pi under any sequence of the kernels. Consequently a nonempty selected set has entropy H(pi)+sum_j H(l^(s[j+1]-s[j]),t). Empty selections have entropy zero, and singleton selections have entropy H(pi).

For N=n+1 fair selected coordinates, a fixed pair at gap i is consecutive precisely when its endpoints are included and the i-1 intermediate coordinates omitted. The other N-i-1 coordinates are free, giving 2^(N-i-1) selections. There are N-i such pairs. There are 2^N-1 nonempty selections. Thus

2 sum_S H(X_S)/2^N = 2(1-2^(-N))H(pi) + sum_(1<=i<N) (N-i)2^(-i)H(l^i,t).

The block entropy is H(pi)+(N-1)H(l,t). Divide the preceding identity by N and subtract this normalized block entropy. The initial boundary term vanishes. The remaining triangular series converges by dominated convergence: its coefficients lie between zero and one, converge pointwise to one, and 0<=H(r,t)<=log 2. Therefore actual rank-zero uniform intricacy equals

F(l,t)=sum_(i>=1) 2^(-i)H(l^i,t)-H(l,t).

On t=0, F extends continuously to l∈[0,1], vanishes at both endpoints, and is strictly positive inside. Indeed l^i<=l and binary entropy is increasing on [0,1/2], with strict inequality at i=2. Compactness yields an interior diagonal maximum l0.

The coefficient of t² in H(r,t) is

c(r)=-(1-r)/2 log((1+r)/(1-r))-(1-r)/(2(1+r)).

Actual differentiation establishes H_tt(r,0)=2c(r). Further c'(r)=one-half log((1+r)/(1-r))-r/(1+r)^2 and its derivative is 4r/((1-r)(1+r)^3)>0. Since c'(0)=0, c is strictly increasing on [0,1). Thus every difference c(l^i)-c(l) is nonpositive, strictly for i=2, and their geometrically weighted sum is strictly negative.

Termwise differentiation is justified on [0,b]×[-delta,delta] for any b<1 and delta<1. The two entropy arguments remain strictly between zero and one. The explicit first and second transverse derivatives are continuous on this compact rectangle and therefore uniformly bounded, independently of every gap power. Geometric majorants justify two successive differentiations. The second derivative series is jointly continuous and F_tt(l,0)<0 for each 0<l<1.

Near (l0,0), joint continuity makes F_tt negative throughout a rectangle. For each fixed nearby l, F(l,·) is concave on the transverse interval. Swapping labels makes F even in t. Concavity applied to t and -t shows F(l,t)<=F(l,0). Diagonal maximality gives F(l,0)<=F(l0,0). This proves a full two-dimensional local maximum without any assertion of uniqueness or strict longitudinal curvature.

For matrix diagonal coordinates z=(u,v), the inverse chart is l=u+v-1 and t=(u-v)/(2-u-v). The denominator is positive near the chosen matrix, so the inverse is continuous and transfers this maximum to the actual finite-subset source limit.

Finally consider ALL stationary one-step binary Markov probability laws, represented by an arbitrary stochastic matrix in the closed unit square and any normalized stationary initial vector, with cylinder probabilities as in source (6.1). This includes boundary and nonergodic laws. The weak topology makes clopen cylinder probabilities continuous. Near the witness the two one-state probabilities stay positive, and the matrix diagonal entries are recovered continuously as the ratios of length-two diagonal cylinder masses to their one-state masses. The recovered matrix remains interior. Stationarity and normalization uniquely determine its initial vector; equality on all block cylinders then identifies the law with the constructed one. Thus every law in the relative weak neighborhood is covered, and its actual rank-zero intricacy equals the source functional at its recovered matrix. The parameter maximum transfers to a local maximum among the entire stated law class. Full support and invariance under every integer shift have already been proved.

The final Lean theorem explicitly asserts full support, every integer-shift invariance, membership in the full stationary one-step class, convergence of actual finite intricacy at the witness, and relative weak-topology local maximality. It asserts no global optimum, uniqueness, optimization over arbitrary invariant measures, or higher-order extension.
