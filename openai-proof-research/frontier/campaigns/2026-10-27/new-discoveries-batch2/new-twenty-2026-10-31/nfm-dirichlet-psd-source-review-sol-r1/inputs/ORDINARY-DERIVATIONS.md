# Sustained ordinary routes, no mathematical execution

## 369624: Lee one-symbol codes

Actual 2508.01702v4 (28Apr2026), Conjecture1, Definition4 and relevant Lee-weight/modular-sum constructions read. Definition4 requires d_L(Enc(u),Enc(v))>=2t+1 whenever function values differ. For modular sum, the triangle inequality gives d_L(Sm(u),Sm(v))<=d_L(u,v). Thus a sufficient multiplier condition is

d_L(p*x,0)>=2t+1-x for each integer 1<=x<=2t.

For Lee weight, ordinary absolute weight difference is <=d_L(u,v), so the same condition for ordinary differences <=2t suffices. If the difference is larger than2t, the message distance already suffices. No conclusion for the separately defined Lee-weight DISTRIBUTION function is asserted without its actual definition/bridge; its passages were not fully recovered.

At Q=2t(t+1)+1 and p=2t+1 one can prove the scalar condition symbolically. For 1<=x<=t, px is between0 andQ, px >=2t+1-x, and Q-px >=2t+1-x because their difference equals 2t^2-2tx>=0. For x=t+j, 1<=j<=t, px-Q=(2t+1)j-(t+1) lies between t and Q; its difference from the required t+1-j is 2(t+1)(j-1)>=0. The other circular distance Q-(px-Q) minus (t+1-j) equals 2t^2+2t+1-2tj, positive for j<=t. Therefore both candidates in the circular minimum satisfy the bound. For t>=2 this p belongs to [2t,floor(Q/2)]. For t=1,Q5, p3 is outside that interval but its negative representative p2 has identical Lee distances. This is a source endpoint/range issue, not a significant refutation or new family.

This endpoint calculation does NOT extend monotonically to all q>=Q. For example the same p5 at t2,q15 collapses x3 to zero, violating the required positive parity distance. This disproves that mechanism, not the target: another p might work. The general problem is to choose an integer slope whose short multiples avoid all forbidden arcs around qZ, equivalently a cyclic lattice avoiding the finite Lee diamond. An area/counting lower bound q>=Q only gives a necessary packing condition; it does not supply a cyclic lattice of every determinant q or a p in the specified interval. A two-parameter interval selection/Euclidean-lattice route still lacks that all-q covering lemma and the distribution-function bridge. No enumeration/CAS/numerical experiment was used. This is parked, no full candidate.

## 377198: cubic giant component

Actual full eight-page math0106022v1 extracted text read, including median half-volume definition of p^G and the context before Conjecture3.2. The source explicitly discusses finite TRANSITIVE graphs before the local-limit setup; the corpus literal omits that word. A disjoint union of two high-girth expanders, or two such blocks joined by a small cut while preserving degree, can suggest multiple giants and a half-volume threshold bounded below1 if one block exceeds half. That route does not preserve transitivity. It is therefore not a source-faithful negation, even if one later supplies all probabilistic details. No full example claimed.

A second route starts with local tree exploration. For every fixed radius R and sufficiently large girth, the exploration agrees with the cubic tree, with offspring2 beyond the root. For p>1/2 this supplies positive survival probability to distance R. It gives no control at a radius comparable with graph size and no identification of exploration clusters from distinct roots. Turning local survival into linear volume requires a global expansion/sprinkling bound. The supplied assumption p^G<=p0<1 concerns a half-volume component at p0, but does not itself compare p0 to every fixed p>1/2.

A third route uses Theorem1.1: weak concentration plus logarithmic diameter gives uniqueness after sprinkling. The source explicitly observes that this concentration property need not hold even for transitive logarithmic-diameter graphs. Growing girth and bounded median threshold have not been shown here to imply that hypothesis. The exact unpaid lemma is a uniform global merging/exploration result for the full transitive high-girth sequence at EVERY p>1/2, or a source-faithful transitive counterfamily satisfying the threshold condition. The exact-size phrase Cp|G_n| is informal giant-size language; no divisibility objection is counted. No finite/nontransitive/domain wording correction earns credit.

## 352259

Full all-parameter author proof and the competing significance assessments are in FULLCANDIDATE.md. Initial affine-weight intuition was discarded upon reading the actual logit definition; no affine-weight proof is offered as source fidelity. Pure-node and all-positive shortcuts were repaired by a fixed open cap and negative-mass control.

## 360389: exact source-owned consequence, zero

Actual 2310.10983v1 Section1.2 prints Reformulation2 exactly equal to the target. Its equivalence discussion and locality Theorem1.1 are read and attributed, not the deep whole-paper proof. A complete finite-size-to-target deduction: apply Reformulation1 with sprinkle epsilon/2 at p=pc(G)-epsilon. If the sphere probability were at least delta at its uniform radius, percolation at pc-epsilon/2 would be positive, contradicting definition of pc. Thus for every delta>0 there is a uniform radius after which the sphere tail is below delta, by monotonicity in radius. Define h(r)=sup_G P_pc-epsilon(o<->S_r)+1/r; it is positive and tends to zero. Negative parameter cases use the conventional zero-edge extension, or the target must be read only where pc>=epsilon. This is a convention issue, zero credit. The source's lack of an EXPLICIT numerical h does not mean nonexistence of h. Exact source-owned result, no new outcome.

## 360867: exact public source theorem, zero

Actual 2311.15013v2 Theorem1.2 asserts Conjecture1.1 in entirety, whose two clauses match the literal. Theorems1.4/1.5 give common asymptotic factor with positive constants alpha_h,beta_h; Theorem1.6 gives ratio>1. The closing proof on page26 compares the constants and concludes allh>=2. Therefore choosing any ratio margin between1 and gamma_h gives the eventual inequality, including non-strict >=, and asymptotic positivity of b_h makes the ratio meaningful eventually. Actual main theorem, definitions, comparison proof and supporting statements were read; circle-method and intermediate coefficient identities were not fully audited. Public source-owned claim/proof, not a new proof certificate. A printed n/h limit typo in surrounding prose does not change the explicit Theorem1.2 matching statement and is not credited.
