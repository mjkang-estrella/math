# r35 mathematical work — zero nominations

## 343269: polygon-chain determination (rank 1, source-definition hold)

Read the actual July 2019 source: introduction/group definitions, cycle presentation discussion, Theorem 4.4 and its generator argument, and concluding Conjecture 6.1 (printed p19). The phrase is “a maximal induced path” and then “unique polygon chain decomposition corresponding to the maximal path decomposition”. No explicit rule for treatment of branching vertices is supplied there. A maximal induced path through a branching vertex is not the same as a maximal run of degree-two vertices. This is a material source gap, not an opportunity to redefine the question.

First route: use the inner-dual cycle presentation, with diagonal face lengths and -1 for adjacent faces. On a double-star dual, order four leaf faces first and two central faces last. Put leaf lengths (3,3,4,4), central lengths (u,v), join leaves 0,1 to u and 2,3 to v and join u to v. The two integer matrices are explicitly recorded in polygon-diagnostics.json. Swapping (u,v)=(4,5) to (5,4) keeps the central two-face chain determinant uv-1=19 and the four singleton values 3,3,4,4. Sympy Smith diagonals are respectively (1,1,1,1,6,336) and (1,1,1,1,1,2040). These are diagnostics, not a source counterexample or a kernel certificate.

Second route: explain the arithmetic mechanism rather than search further. Modulo 3 the first two leaf equations force central coordinate x=0 and leave a difference between the two leaf coordinates free. The other leaf coordinates equal y/4. The final equation becomes (v-1/4-1/4)y=0. At v=5 this coefficient vanishes mod3; at v=4 it does not. Thus a second mod3 null direction appears in the first matrix, while the second has only one. The u-equation determines the sum of the first two leaf coordinates from y. This gives exactly nullities 2 and 1 over F3, independently checking the Smith diagnostic's 3-primary distinction. It explains how central coupling could defeat determination by detached chain counts.

Third route/objection: if maximal induced paths include their branching endpoints, the proposed invariant list is wrong. For example the two left leaves together with u give the tridiagonal path determinant 9u-6, which changes from30 to39. Thus the candidate does NOT survive that interpretation. No graph-presentation theorem or change of decomposition has been silently assumed.

Remaining gates: establish the intended source decomposition from an explicit primary definition, prove both actual embedded outerplanar graphs realize the same literal input data, certify the sandpile/cycle presentation and generator number, check later prior art, then formalize all of those semantics. Because the first gate is material, park here; no further access hunt and no Lean investment. The phenomenon itself is not claimed novel.

## 343332: minimum-weight MIPPR word (rank 2, sustained incomplete)

Read the published IEEE IT67(11)(2021)7458–7476 author-hosted PDF, p7463 definition (3), MIPPR definition, full Lemma6 proof and covering-design bridge; p7470 Conjectures47–48. The reserved claim is Conjecture48, not the stronger47. 'Minimal' is treated conservatively as minimum cardinality N(L,s,r), consistent with the paper's optimization problem, rather than merely inclusion minimal.

For a code C of s-subsets of [L], identify binary words with supports Y. The exact defining condition is

    |Y| <= r iff for every c in C, |Y symmetricDifference c| <= r+s.

Since |c|=s, all low-weight Y satisfy the right side automatically. Thus each Y with |Y|>r must be excluded by a selected codeword c having |Y|-2|Y intersect c|>r. An MIPPR word is exactly an inclusion-minimal transversal of C, and its smallest weight equals the transversal number tau(C). Lemma6's r+2 extension argument gives tau(C)>=r+3. Selecting one point in each codeword gives tau(C)<=|C|. Consequently every code attaining the lower cardinality bound |C|=r+3 satisfies48. This bridge is routine and not a nomination; it isolates the genuinely remaining case N(L,s,r)>r+3.

Second route: formulate exact finite set cover on ALL Y with |Y|>r, not just weight r+2. To seek a counterexample impose also, for every (r+3)-subset T, a selected codeword disjoint from T, forcing tau>=r+4. attempts.py solves both problems in five small parameter triples. Solver-reported minima (ordinary / tau>=r+4 constrained) are:

    (5,2,0):4/10; (7,3,0):5/12; (8,3,0):4/8;
    (9,4,0):5/12; (8,3,1):8/20.

Each returned code was independently checked against the literal ball identity by integer bit arithmetic over all 2^L words, and tau was recomputed exhaustively. The solver's lower bounds/optimality claims are NOT proof certificates. No Lean conclusion follows, including for these parameters. Larger-tau valid codes exist, but none returned at the unconstrained minimum cardinality. This directly blocks the attractive but incorrect shortcut “any valid code with tau>r+3 refutes48”.

Third route: cardinality-minimum C must be irredundant as a cover of the excluded Y. Every c therefore has a witness Y_c excluded only by c. This is weaker than the desired small transversal: it only forces |Y_c intersect c| to be below its threshold while all other intersections are above threshold. No argument converts these heterogeneous thresholds to one common transversal of size r+3. The exact missing lemma is: if an s-uniform PPRIC family has tau>=r+4, construct a STRICTLY smaller s-uniform family preserving exclusion of every Y of weight>r. Neither arbitrary edge deletion nor the covering-design restriction to r+2 subsets proves that lemma. Park rather than broaden finite sweeps.

Remaining formal work if a witness is later found: certify a global cardinality lower bound N, literal ball identity for the exhibited code, tau>r+3, and the binary-word/support bridge. A code-validity checker alone cannot discharge cardinality minimality.

## 343349: join formula (routine boundary route, no nomination)

Read source introduction, Lemma2.2 and full spectral-projection proof, Lemma2.3 and independent-set proof, minimum-positive-semidefinite-rank definition/Lemma2.5, and Conjecture5.3. The introduction explicitly states the complete classification of graphs attaining [n-1,1]: a clique with isolated vertices. This supplies a full routine bridge for a disconnected-input boundary failure.

Take G=H=K2 disjointUnion K1. The PSD matrix with 2x2 block [[1,1],[1,1]] and a zero isolated row has rank1 and two distinct eigenvalues0,2. No graph with an edge has q=1 or mr+=0, so q=2, mr+=MB=1. The join is connected and noncomplete. By the source's already stated [n-1,1] classification it cannot have MB=1, contradicting the asserted maximum1 if the literal unqualified graph domain is used. This is completely supplied by that classification and an isolated-vertex domain issue: excluded as routine/domain correction, not a new significant solution. No formalization is warranted.

An attempted substantial connected-input route would represent G and H by Parseval frames and rotate to make all cross inner products nonzero. For unequal ranks, concatenated frames do not automatically remain Parseval in the larger space: a rotated smaller projection plus a scalar identity is not scalar identity unless the smaller projection is trivial. Thus generic nonvanishing alone does not prove the conjecture. No connected-case theorem claimed.

## Other source reading

342793: Xiao–Tompkins Conjecture4.3 is proved by the stronger induced Theorem4.4. Read its proof: circular-basis weighted inequality from Remark4.2/Lemma4.5, then the zero/full-subspace cases. Noninduced-free implies induced-free; the k middle levels supply the matching construction. Known, zero credit.

342841: Chen–Lu–Ye Observation2.3 and complete proof constructs a cycle of q copies of K(r,r) with one edge deleted, rejoining endpoints cyclically. Their fort argument proves gamma(p,r-3)=2q for n=2qr, exceeding n/(r+1). Known exact refutation, zero credit. 342842 is a different Conjecture4.1; read its statement and surrounding construction/Theorem1.6 scope, but not its long proof (only l=2,3 proved). General l>=4 remains unproved here.

343283: read Chatwin Conjecture8, reduction context, Theorem45 and its preceding induction completion pp43–44 (PDF extraction labels preserved). Theorem45(1) states exactly g(P)=g(P') for N>0; the proof invokes Proposition38 and Lemmas33–34. This is a known-source resolution; not an independent audit of the entire long algorithm proof.

343345: read Hammonds Conjecture6.3 and definitions. Hu–Peng–Wang, AIMS Mathematics8(3)(2023)6697–6704, Theorem1.6(1)–(2), full proof pp6701–6702, proves the formula. For n=2^k, the least nondisivor ell>=2^d is 2^d if k<d and 2^d+1 if k>=d, giving exactly their two cases. The proof uses the binary cube lower witness in the first case and Property D plus zero-sum extraction in the second, with Theorems1.2/1.5 and Harborth bounds. Earlier dependencies accepted as cited, not independently re-proved. The first attempted AIMS URL ended339 vs338 incorrectly: math-08-03-338.pdf is a DIFFERENT fuzzy-contractions paper, retained as a wrong-document receipt and never relied on. Correct resolution is math-08-03-339.pdf, DOI10.3934/math.2023339.

343233: read source pp10–11 heuristic and Conjecture1, plus Theorems6–7 and actual elimination proof. The latter only bounds existence of finite-complex realizations, not order-independent termination of the heuristic. Scalar splitting and permitted residual operations are not fully specified by that informal example. No arbitrary algorithm was substituted. Source-gap hold.

343185/343186: inherited r226 actually studied the same survey Conjecture3.15 and signing family (source-URL history hits, not ID hits). Retain those defer decisions. Fresh source passages confirm integer Gram semantics and the one-sided vs two-sided eigenvalue distinction. No low-maximum-degree wording trick receives credit.

343384: source alias/ID history reveals substantial prior ordinary proof and investment reviews; review r3 says INVEST, not accepted. Retain that inherited candidate and stop duplicate investment. No new primary review credited for this item.
