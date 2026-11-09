# Ordinary attempts and exact gaps

No result in this file is a qualified candidate. All execution plans remain unauthorized; no solver, numerical enumeration, Lean or child agent was used.

## 341439: signed binomial-Eulerian coefficients

Exact endpoint: every adjacent coefficient minor a_j^2-a_(j-1)a_(j+1) of tilde A_n(t,-1) is nonnegative for every n>=1. The latest primary source states this as Conjecture 5.2, rather than Theorem 1.3 (which establishes symmetry and unimodality only). V1 has the corresponding Conjecture 7.2; v2 and v3 have Conjecture 5.2. We read relevant version paragraphs, not all pages of every version. The version of record was identified as European J. Combin.78 (2019),105-120, DOI10.1016/j.ejc.2019.01.010. DOI returned a redirect shell; direct linked article returned403. No denied-route retry or alternative publisher API was attempted. This blocks qualification regardless of the ordinary route.

First route: use the source section4.1 Jacobi-Rogers expansion for A*_m(t)=1+t sum_(k=1)^m binom(m,k)(1+t)^k A_k(t). Its path factors are b_h=(h+1)+(2h+1)t+(h+1)t^2 and lambda_h=h^2 t(1+t)^2. Each b_h is coefficient-log-concave because (2h+1)^2 >= (h+1)^2; lambda_h is log-concave. Products are log-concave by convolution with no internal zeros. The source uses the fact that all these path terms have the same center m to infer unimodality of their sum. This last step does NOT infer log-concavity. Explicit obstruction to that deduction: the centered, individually log-concave sequences (1,1,1,1,1) and (0,0,10,0,0) sum to (1,1,11,1,1), whose minor at index1 is1-11<0. This is a counterexample to an inference, not to the MathDB conjecture.

Sustained next step: if f_P,j denotes coefficient j of the term for weighted path P, it suffices to prove, for each pair P,Q and j,
2 f_P,j f_Q,j >= f_P,j-1 f_Q,j+1 + f_Q,j-1 f_P,j+1,
then sum over P,Q. No proof of this synchronization property is known here. The common symmetry center and individual log-concavity alone are insufficient. A weaker aggregate mixed-minor inequality over all pairs would also suffice. Neither is silently assumed.

Second route: try a differential or interlacing induction using Corollary2.4, retaining both even and odd rows and the signed Eulerian auxiliary rows. The recurrence has a negative sum in the even update, so coefficient positivity/log-concavity is not preserved termwise. Ordinary real-rootedness is unavailable even at A*_1=1+t+t^2 (nonreal roots); this defeats a generic real-interlacing/Newton route, without disproving log-concavity. Needed lemma: a simultaneous adjacent-minor induction controlling that subtraction, or a new positive combinatorial injection from the product of rank j-1 and rank j+1 classes to two rank-j classes. No such injection has been constructed. Printed first values were read as source examples, not recomputed in a search.

## 344794: Clar covers, distinct from sextet patterns

Exact objects: H is a finite connected plane graph without cut vertices, interior faces regular unit hexagons; source works with perfect-matchable systems. A Clar cover is spanning with components edges or hexagons. c(H,k) counts COVERS with k hexagon components. s(H,k) instead counts only the resonant HEXAGON SET; different residual perfect matchings contribute separately to c. The literal chi(H,x) is the former polynomial. We do not replace it by the sextet polynomial.

First route: source paragraph following Conjecture 4.4 states chi(H,x)=phi(H,x+1), where phi counts perfect matchings by number of proper sextets. Positive coefficient log-concavity is preserved by x->x+1. However log-concavity of phi is itself Conjecture 4.4, so this is a conditional bridge, not a proof. Thin systems additionally have phi=sigma. Source real-rooted pyrene/nonbranched families cover only subclasses. No argument extends their recurrence to peri-condensed H. A proof needs either all-H phi log-concavity or a direct inequality for its binomial transform, not just special families.

Second route: chi(H,x)=C(R(H),x), the cube polynomial of the resonance graph, which is median. Xie-Feng-Xu2303.14671 Theorem 1.1 relates cube polynomials to shifted clique polynomials of crossing graphs; Theorem 1.2 says every graph is a crossing graph of some median graph. These do not say every median graph is a HEXAGONAL RESONANCE graph. Their section4 gives Q_n (n>=9) with sufficiently many attached pendants as explicit nonunimodal cube-polynomial examples. The proof changes only coefficients0 and1, while alpha3>alpha2 survives. Section5 explicitly retains the resonance-graph conjectures5.1/5.2. Thus a theorem for all median graphs is false, and transplanting their obstruction requires a perfect-matching-preserving, plane unit-hexagon realization. No such realization was proved. This is not a valid counterexample to344794.

Precise next lemma: construct an actual 2-connected unit-hexagon system with resonance polynomial equal to a specified pendant-cube polynomial, or prove a structural restriction on resonance crossing graphs that gives log-concavity after shift. Arbitrary simplex-graph realization is insufficient. Even a successful transplant of the printed example would trigger the existing source-example-adaptation significance gate. MathDB357860 is the same conjecture, not another solution. Journal MATCH84(2020),217-228 web body excerpts retain this conjecture; its PDF request timed out. Complete journal and citing proofs remain HOLD.

## 343528: weighted admissible subdivisions

Source definitions read: weights phi(v)>=0 sum to1, and phi(Q)=sum_v phi(v)^2+sum_ab in E(Q) phi(a)phi(b). An induced Q' is H-admissible if a bijection b and order on V(H) satisfy: for each edge xy of H with x<y and b(x)b(y) a nonedge of Q', every later z distinct from x,y fails at least one of the two adjacencies to b(x),b(y). The condition concerns later common neighbours of NONEDGES; it is not ordinary subgraph containment.

Route1: use forbidden clique/independent sets. Either homogeneous t-set is K_t-admissible, hence s=|V(Q)|<R(t). Weighted Turan symmetrization gives only
phi(Q)>=1/(2s)+1/(2(t-1)).
This is the source Theorem 18 / journal Theorem 3.3 proof. Its bound is strictly below1/(t-1) whenever s>t-1; the residual gap is1/(2(t-1))-1/(2s). Replacing Ramsey with a finite support cap does not fill it.

Route2: extend Proposition 13 (journal2.12) structural proof for t=5, using forbidden admissible partial subdivisions. Its local observations force constrained five-vertex patterns and a small support. Removing branch vertices from a forbidden K_t subdivision does not imply absence of K_(t-1) admissible subdivisions: a smaller admissible configuration may fail to extend at all, and its ordering constraints change. No induction is justified by that deletion.

Next mathematical lemma: an all-t replacement for the support/weighted-case argument that yields the missing quadratic gap while preserving the exact later-common-neighbour condition. No such lemma proved. Fixed-t finite verification would not resolve all t and is neither proposed nor executed. Actual latest journal Conjecture 3.2 agrees with arXiv Conjecture 17; no resolution inferred from that open label.

## 340567: a complete, uncredited indexing diagnosis

Take P3 with vertex order endpoint, center, endpoint. D=diag(1,2,1). Its normalized Laplacian is
[[1,-1/sqrt(2),0],[-1/sqrt(2),1,-1/sqrt(2)],[0,-1/sqrt(2),1]].
The independent vectors (1,sqrt(2),1), (1,0,-1), (1,-sqrt(2),1) have eigenvalues0,1,2, respectively. Hence descending mu1=2,mu2=1,mu3=0. With bipartition sizes2,1 and2 edges, rho=1. The printed product from i=1 to n-2 is2, violating2<=1. No mathematical search was used.

Actual source Conjecture 5.8 prints this ordering/product and the adjoining sentence incorrectly calls the SMALLEST positive eigenvalue equal to2 for bipartite graphs. The normalized-Laplacian spanning-tree identity is tau(G)=(product_v deg(v))/(2|E|) times product_(i=1)^(n-1) mu_i. Thus the Ferrers bound tau<= product_deg/(|X||Y|) becomes product_positive mu<=2rho. Since the LARGEST eigenvalue is2, the equivalent product is mu2...mu_(n-1)<=rho. The literal discrepancy is indexing, not a new Ferrers theorem. Zero credit under correction precedent; no candidate or Pi endpoint.
