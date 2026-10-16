# Mathematical checkpoint 2 — interval location and simultaneous span

Original prose CC BY 4.0. No contribution verdict.

Boundary reconstruction: write l for the preorder index of a nonleaf w,
r=l+|T_w|, d=H(w), and append H_N=0. Then H_l=d,
H_{l+1}=d+1, H_j>d for l<j<r, and H_r<=d. The component
of the interpolated {H>d} containing a proper descendant starts at l/N
and ends within [(r-1)/N,r/N]. Thus its endpoints differ from the
full subtree-cell endpoints by <=1/N (and from the root-omitted subtree
by <=1 cell at each endpoint). Leaves have no such component, but their
only possible occurrence on an ancestral path is the final self term.
Deleting the global root and changing to M cells moves coordinates by
<=1/N. Variable sampling times converge to the fixed time t as well.
For a.e. (t,z), endpoint monotonicity and the sandwich at z+/-epsilon
then imply convergence of the ancestor interval. The exceptional levels
are countable for each t, so Fubini and dominated convergence apply.
Preorder jumps can exceed one; tightness of continuous h_N makes their
rescaled maximum vanish. No contour assumption is needed.

For phi vanishing on s<=delta, F=phi/s has a Lipschitz extension by zero.
Nested intervals on any path have endpoint variation <=2; hence F has
uniform bounded variation. With C_j=sum_{i<=j}(b_i-theta), Abel summation
bounds the weighted discrepancy by max|C_j| times
(||F||_infinity+Var_path F). Source bounded path sums pay max|C_j|.
The depth mesh sigma/(2sqrt N) gives the factor 2/sigma. Coarea over t,z
then pays interval locations as well as sizes, jointly with h_N.
The thinning constant is (2/sigma)*(p_2/2)=p_2/sigma.

For simultaneous injectivity, fix a good CRT realization and a countable
dense set of leaves. Their root paths cover the skeleton; their rational
arc subintervals form a countable length-positive basis. Conditional
Poisson marks meet each basis subinterval a.s., because the intensity as
r decreases to zero is infinite. On this single event marked clade
indicators approximate every regular cut along an arc in L2(mu).
Choose countably many dense regular cuts on these countably many arcs.
They separate every pair of leaves; laminar intersections make their span
with constants an algebra generating the standard Borel leaf space.
Monotone class gives L2 density. No fixed-g probability argument or
independence of nested fringe marks is used.
The coding map is a.e. one-to-one: two distinct coding times at a leaf
would force either a strict descendant or an atom. Both are excluded by
Aldous CRT III Section 2.3/Corollary 22. Thus there is no unaddressed
orthogonal complement in H0=L2_0[0,1].

Finite independent word enumeration (not candidate code): 305 valid
words, 126 selected-child equalities, 1252 nonleaf component cases,
including preorder descents of size 8 and a unary law probing m=0.
These checks do not prove any limit or the dense-span assertion.
