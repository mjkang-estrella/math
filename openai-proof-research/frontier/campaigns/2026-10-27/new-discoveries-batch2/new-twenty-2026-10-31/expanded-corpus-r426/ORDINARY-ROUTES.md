# Ordinary investigation; no novelty or acceptance claim

All mathematics here was reasoned ordinarily, without mathematical programs, enumeration, numerical tests, CAS, solvers, Lean, or compilation.

## 327602: full exact refutation, already public

For every odd n=2k+1>=5, take K_n and remove a matching covering exactly 2k vertices. The uncovered vertex has degree n-1; each other vertex has degree n-2. The uncovered vertex is universal, so the graph is connected, simple and nonregular. In the unordered-pair version of source definition(2), exactly n-1 pairs have unequal degrees, each difference1. Thus irr_t=n-1<2n-4. The smallest displayed witness is K5 minus two disjoint edges; its degree list is (4,3,3,3,3) and total irregularity4<6. This is an ordinary symbolic construction, not an enumeration.

Initial alternatives considered a single exceptional degree below the others and parity of the degree sum. Taking an exceptional odd degree with all other degrees even on odd order violates handshake parity, so that shortcut fails. The universal-vertex construction pays graphicality and connectedness explicitly. A separate lower-bound route partitions a nonconstant integer degree multiset by a threshold: at least a(n-a)>=n-1 unequal pairs cross the threshold. This proves the universal n-1 lower bound without graphical classification; the construction proves sharpness for odd n. It does not prove the sharper even-order classification without parity refinements.

Prior gate: Abdo–Dimitrov1407.1276v1 (4July2014), Lemma2.2 immediately following its proof explicitly constructs K_n minus a matching, and Theorem2.1 treats the n-1 bound. Same graph, same invariant and quantifier refutation. Contrary significance: an explicit five-vertex witness is useful for formal fidelity and disproves the full conjecture, but the exact family and endpoint are already public. Zero credit; not an invented earlier printed claim.

## 328423: two full ordinary routes on the source meaningful domain m>0

Put S=sum over unordered edges uv of sqrt(d_u d_v), and R=sum over those edges of 1/sqrt(d_u d_v). For connected n>=2 all degrees are positive. Let B=D^(-1/2) A D^(-1/2). For every real vector x,
|x^T B x|<=sum_edges (x_u^2/d_u+x_v^2/d_v)=||x||^2,
using 2|ab|<=a^2+b^2. For an orthonormal eigenbasis u_i of the real symmetric A, trace(AB)=sum_i lambda_i u_i^T B u_i<=sum_i |lambda_i|=E. But trace(AB)=2R. Cauchy applied to sqrt(sqrt(d_ud_v)) and its reciprocal over the m edges gives SR>=m^2. Consequently E>=2R>=2m^2/S=n/epsilon. There is no simultaneous-diagonalization assumption: each u_i has a Rayleigh quotient of B in [-1,1]. The formula is not defined for the isolated one-vertex connected graph; treating that as a new counterexample would only be a domain correction.

Second route uses vertex energies e_v=(|A|)vv. By the symmetric spectral decomposition and Cauchy, for adjacent u,v,
1=|A_uv|<=sqrt(e_u e_v).
Summing e_u/d_u+e_v/d_v over unordered edges yields sum_v e_v=E. Each edge contribution is at least2sqrt(e_u e_v/(d_ud_v))>=2/sqrt(d_ud_v). Thus again E>=2R, followed by the same Cauchy step. Failed shortcut: E>=2m/lambda1 only gives n/beta; beta>=epsilon points the wrong way to deduce n/epsilon. Neither the regular case nor this spectral-radius shortcut settles the target.

Complete prior bridge: in Arizmendi–Arizmendi2106.16044v1, Theorem6 and its actual Theorem4-based proof establish the stronger energy–Randic bound for finite loopless digraphs. Replace every undirected edge by its two opposite arcs. This meets their simple-digraph definition E subset VxV, allowing opposite arcs. Both in/out degrees equal the original degree. Their Randic definition is one half of the arc sum, hence equals R. Their Nikiforov energy is the sum of singular values; the symmetric adjacency matrix has singular values |lambda_i|, hence this equals literal E. Theorem6 therefore gives E>=2R on every meaningful literal instance; SR>=m^2 supplies exactly the requested denominator. No final-journal delivery is needed to authenticate this existing public preprint proof.

Contrary significance: the normalized-adjacency argument is concise and resolves all nontrivial connected graphs, and shortness alone would not defeat significance. But the complete stronger-public-theorem-to-target bridge above needs only this explicit Cauchy step and normalization. This is a routine adaptation with zero credit, not a novelty HOLD based only on a search title.

## 328727: valuation route, repaired by an already public proof

The squarefree reduction to a product of fields loses nilpotent information for repeated factors. Simply replacing each residue by a unit also fails: a polynomial divisible by an unsaturated irreducible factor has no unit replacement with the same action at that component. Saturating every prime power first might cost too many sequence terms; the needed budget is group-theoretic, not just the total polynomial degree.

The successful full mechanism is public: Wang1409.2077v3 Theorem1.1. It uses strict stabilizer growth along a shortest subsequence whose product has the same truncated valuations as the whole product, bounds the remaining quotient-group Davenport constant, and makes unit replacements by CRT only on the already saturated components. ClaimA proves that different truncated valuations give different unit stabilizers using a scalar outside {0,1}; this is precisely where q>2 enters. The resulting nonempty removable subsequence preserves the product, with the empty retained subsequence allowed as in the original definition. The source paper1409.1313 has the same conventions.

Complete scope bridge: for any prime p>2 set q=p. For nonconstant f, (f) is nonzero and proper and R=F_p[x]/(f) is a nonzero finite ring, different from the full polynomial ring. Rescaling f by its leading coefficient does not change its ideal. Wang's semigroup SR and unit group are literally the assigned objects. Thus his theorem proves the entire target. Publication/preprint chronology2014/2015 predates this lane. Contrary significance: an all-multiplicity proof would be substantial in isolation, but this is the exact public solution and receives zero, rather than credit for rederiving its stabilizer argument.

## 328498: independent finite arithmetic, own source already refutes

For K_(a,b), Q acts as bI on the sum-zero subspace supported on the a-part (dimension a-1), as aI on the b-part sum-zero subspace (dimension b-1), and as [[b,b],[a,a]] on vectors constant on each part. The last matrix has eigenvalues a+b and0. These invariant spaces have total dimension a+b, so this pays all eigenvalue multiplicities without a computer.

Take a=2,b=4,alpha=5. The nonzero eigenvalues are6,4,2,2,2. Hence S5=6^5+4^5+3*2^5=7776+1024+96=8896. The claimed bound for n=6 is6^5+4*3^5=7776+972=8748, smaller by148. Both the alpha>1 hypothesis and bipartiteness hold. Connectedness holds even though the literal does not require it. Alternate routes explored balancing at alpha2/3 and dominance of an unbalanced second eigenvalue at large alpha; a majorization argument favoring balance cannot hold for every alpha.

Prior gate: the assigned source Ashraf1408.0639v1, Conjecture3, Lemma6 and Theorem7 proof explicitly refutes this same alpha>1 claim with complete bipartite graphs for alpha>3. Its printed formula specialized at (a,b,alpha)=(2,4,5) gives exactly this witness. Contrary significance: the finite exact refutation is formally economical, but is a parameter instance of its own source's solved family. Zero credit, no candidate dispatch.

## 328752: exact public corollary

Liu–Tang–Zhang2607.18031v1 Theorem1.2 proves the connected square-energy assertion. Corollary4.1 states the precise assigned disconnected inequality. Its proof uses the block diagonal adjacency matrix, additive positive/negative square sums, and sum_i(n_i-1)=n-kappa. Isolated components contribute0 on both sides, and the empty graph also has0=0. Theorem2.1's matrix inequality proof and the entire deduction of Theorem1.2 were read, rather than inferring a proof from the abstract. Contrary significance: the disconnected quantifier does not create a new result because that very quantifier and component bridge are explicitly public (20July2026). Zero credit. No public Lean source was executed or re-audited.
