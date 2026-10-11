# I169 — bridge independence: deleting the deleted-edge coordinates

Date: 2026-10-10. Technical research; no acceptance or literature-novelty nomination.

**Outcome.** I168's R168/E168, D168, M168, histogram and mandatory cases all pass independent audit. The universal exchange inequality remains open. New results prove (1) an exact reduction entirely inside the degree kernel of the deleted-edge graph, (2) `t >= ell-1` whenever the expanded face is a quadrilateral, and (3) exchange, with an explicit nonzero bridge coefficient, for **every side-face expansion of every even prism**. The latter includes an infinite family with unbounded survival loss. No counterexample to exchange, (T), or Q164 was found.

All theorems in the OpenAI repository at revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. No upstream truth audit, ex-falso argument, or contradiction extraction is used. The actual `cor:pfaffian-paths` statement and its stated planar applicability were read in the bound manuscript, lines 812–828. No other upstream theorem is needed below. Wider implications involving the brace theorem and Q164 remain program context.

Only the assigned report and I169 experiment/source directories were written. No ancestor code was read as implementation source, imported, or executed; ancestor JSON was used as data. No subagents, staging, commits, publication, or shared-ledger edits occurred.

## 1. Authentication and independent audit, completed before the attack

The supplied hashes were checked before relying on I168:

- `frontier/iterations/i168-cross-class-exchange.md`: `696a15a676ba0ecd6e90cb196673c3d21e2f8450755113c7ee1a70d6c285db31`.
- `frontier/experiments/i168_cross_class_exchange/seal.json`: `02657bf213e3153512979aeb3ed47618aa4d082597c40d0cf2ae428a3f7fc68c`.

Both match. The seal-bound inventory and every entry in that inventory were authenticated by hashing bytes, without executing an ancestor verifier. I168's non-context external bindings match; context drift is recorded separately. `initial-hash-check.json`, `external-bindings.json`, and the context receipts retain the checks.

The fresh standard-library toolkit uses vertex-path DFS and an independently written edge-decision degree-factor enumerator. It computes spanning endpoint paths directly, and spanning paired two-path covers by their prescribed degrees and component test. Complete edge-set equality checks the six lifted classes against both child enumerators. Integer primitive-row elimination and a separately written Fraction column-sweep elimination cross-check **all 636 main rank computations**, not only selected steps. The bound 15 plane parent graphs and all children are checked for simplicity, cubic degree, bipartiteness, spherical face incidence and 3-vertex-connectivity. No claim of census completeness beyond the specified input is made.

Execution starts with index 0, then 520,522,524,527,528,530,533,534,536,539, then the other indices from 520 through 539, before the remaining census. Thus both I168's original eleven first tests and the requested enlarged mandatory set `{0} union {520,...,539}` are covered.

### 1.1 R168 and E168 — PASS ORIGINAL

Write the expanded face terminals in cyclic order `u,v,...,y,x`, delete `e=uv,f=xy`, and add arms `up,vq,xr,ys` and square `pq,qs,sr,rp`. Set `K=G-{e,f}`. All spaces are over Q (equivalently R for these integer matrices). On the child degree-two affine space use arm coordinates `U_a,V_a,X_a,Y_a` and square coordinates `A_s,B_s,C_s,D_s` for `pq,rs,pr,qs`.

The projection `pi=(U_a-V_a,A_s-X_a)` sends transported cycles to `(0,0)`, and the three new classes `Pux,Pvy,D11` to `(1,0),(-1,1),(0,-1)`. The square degree equations with pi zero give

    U_a=V_a, X_a=Y_a, A_s=X_a, B_s=U_a,
    C_s=D_s=2-U_a-X_a.

This is precisely the affine transport image; reading K and the up,xr coordinates is its inverse. On homogeneous degree kernels the same formula has 0 in place of 2. The code independently checks the image and kernel dimensions using full incidence matrices, not just Hamiltonian differences.

Let L be surviving parent differences and U the three within-new-class difference spaces, embedded with zeros on e,f. Choose C0 surviving and P0,Q0,D0 in the new classes. The three new lift differences have the displayed pi images, whose relation space is exactly `span{(1,1,1)}`. Their sum pulls back to

    b = P0+Q0+D0+2*1_e+2*1_f-3*C0.

Here and below a cycle/path/cover in a vector formula means its edge incidence vector. L, U and b have zero vertex degrees. For b this follows because the three objects have total degree four at each terminal and six elsewhere; adding twice e and f corrects the terminal degrees to six. Changing an object changes b by U; changing C0 changes it by L. Thus

    d(H)=2+dim(L+U+span{b}),
    exchange <=> t+eta >= ell,

where `ell=d(G)-dim L`, `t=dim(L+U)-dim L` and `eta=dim(L+U+span{b})-dim(L+U)`.

Every coordinate identity, complete lift set, degree-kernel identification, representative substitution, and rank identity is checked on all 636 steps. The new argument in Section 2 also proves all six fibres nonempty from the stipulated P4 result, so the representative choices are legitimate universally. The audit does not promote the inequality in E168 to a theorem.

### 1.2 D168 — PASS ORIGINAL

For `L=2k`, the prism dual has cap vertices A,B and rim cycle Z of length L. Root at A. Its two-induced-tree shores are exactly `Z-{z_j}` and the two sets consisting of B plus an alternating rim class.

Here is the exhaustion argument independently reconstructed. If B belongs to the shore, both its rim subset and its complement must be independent, since an adjacent pair with its cap forms a triangle. A bipartition of an even cycle into independent sets is one of the two alternating choices; both induced shores are stars. Otherwise both caps are in the complementary shore. If J is its rim subset, connectivity gives J nonempty, and the tree equation is `2|J|+|E(Z[J])|=|J|+1`. Consequently J is a singleton and the other shore is a path. There are no further cases.

The corresponding L ordinary cycles C_j omit the jth horizontal edge in both layers and use rungs j,j+1. The other two cycles X,Y use every rung and opposite alternating horizontals. These L+2 vectors are affinely independent: in an affine dependence with coefficients a_j,x,y, put S=sum a_j. Top-minus-bottom horizontal coordinates force x=y. Horizontal coordinates then give `a_j=S+x`; the affine coefficient sum gives `S=-2x`. Hence `a_j=-x` and `(L-2)x=0`, so all coefficients vanish for L>=4. Thus d(G)=L+1.

Ordinary shores differ by (1,1). Ordinary/alternating differences are (1,k-1) or (2,k), up to order; alternating/alternating differences are (k,k). For b>=1 and k>=b+2, only ordinary pairs qualify. They form a clique of difference rank L-1; the two other cycles are isolated. This proves precisely the original root-specific bounded-transfer obstruction. It does not exclude an unbounded transfer on one side or non-Hamiltonian intermediate states.

Both cycle enumerators, complete rooted-dual-subset enumeration, D-list equality, transfer counts, and two exact ranks agree for L=4,6,...,16. The graph hypotheses hold: the prism is cubic, simple, bipartite, planar, and deleting two vertices leaves connected layer paths joined by a remaining rung (or an intact layer if both deletions are in the other layer). The proof, rather than the finite range, supplies the universal quantifiers.

### 1.3 M168 — PASS ORIGINAL

The original witness is an order-16 **parent** and order-12 retract; this clarifies the informal opening wording of I168 without changing its mathematical statement. The audited retract edges are

    (0,2),(0,5),(0,9),(0,15),(1,3),(1,5),(1,9),(2,7),(2,11),(2,14),
    (3,7),(3,11),(5,13),(7,12),(9,11),(12,13),(12,14),(13,15),(14,15).

The two selected port pairs are `{(0,5),(0,15)}` and `{(2,7),(2,14)}`, each required to contribute one edge. Fresh enumeration finds 14 unrestricted cycles and exactly eight typed cycles. The 12 degree rows have rank 11; the two additional port rows give rank 13; the typed affine rank is 5, versus ambient dimension 19-13=6. The unrestricted affine rank is 8.

The weight has nonzero values `w(0,2)=1,w(0,5)=-1,w(1,3)=1,w(1,5)=-2,w(2,7)=-1,w(12,13)=1`. Every typed cycle has weight -1. The perturbation supported on `(0,2),(0,9),(2,11),(9,11)` with values `1,-1,-1,1` has zero degree and port sums but pairing 1 with w. This certifies the extra equation directly. No typed-fullness assumption is made in this iteration.

The parent-to-retract edge map is rebuilt from the deleted-edge endpoints and their neighbor triples. The typed cycles are exactly the images of the eight parent cycles avoiding 02. Parent and retract are checked bipartite and 2-extendable by complete perfect-matching enumeration (41 and 24 matchings; 228 and 129 disjoint edge pairs respectively). The plane parent embedding and explicit contraction give retract planarity. This is an exact finite counterexample to typed degree-and-port fullness, not to exchange.

### 1.4 Histogram and mandatory cases — PASS ORIGINAL

The independently reproduced distribution is

    (ell,t,eta)=(0,0,0):138; (1,0,1):385; (1,1,0):56;
                (3,2,1):34; (5,4,1):13; (7,6,1):10.

Index 0 has `(1,0,1)`. Exactly the ten indices listed above have `(7,6,1)`. Every step has `d(H)=d(G)+2` and contains all parent Hamiltonian differences in `L+U+span{b}`. The latter is finite evidence for a stronger containment, not a general theorem. All 21 enlarged mandatory indices pass; I168 itself specified eleven first-test indices, not 21.

One failed implementation is preserved: the first factor enumerator tried to use JSON edge lists as set elements, raising `TypeError: cannot use 'list' as a set element (unhashable type: 'list')` before any mathematical result. Its exact toolkit, empty output and traceback remain. Normalizing those edges to tuples fixed the error. `audit-attempt-02.json` is the successful authoritative audit. This failure is not attributed to I168.

## 2. F169 — a universal reduction entirely inside K

**Theorem F169.** For every admissible C4 expansion G->H in the stated class B, under the stipulated P4 corollary, all six child fibres are nonempty. Choose A in N10, B in N01, C in N11 and P,Q,D in the three new classes. Define

    L0 = diff(N10)+diff(N01)+diff(N11),
    beta = P+Q+D+2*1_e+2*1_f-A-B-C.

Then beta vanishes on e,f and belongs to ker A_K. Moreover

    dim L=2+dim L0,
    dim(L+U)=2+dim(L0+U),
    eta=dim(L0+U+span{beta})-dim(L0+U).

If N00 is nonempty, put `V=diff(N00)`, choose N in N00 and set

    c=N-A-B+C.

Then c also vanishes on e,f and lies in ker A_K, and

    d(G)=2+dim(L0+V+span{c}).

Consequently exchange is exactly the K-space comparison

    dim(L0+U+span{beta}) >= dim(L0+V+span{c}).       (F169)

If N00 is empty, ell=0 and exchange already follows from R168.

**Proof.** Apply P4 in H to the square paths `p-r-s-q`, `r-p-q-s`, `p-q-s-r`, `q-p-r-s`. Since a Hamiltonian cycle cannot close just the new square, their endpoints must use their arms, producing respectively N10,N01,Pux,Pvy. The path `u-p-r-x` forces the other segment `v-q-s-y`, giving D11. The path `u-p-q-v` excludes pr,qs; then r,s force xr,rs,sy, giving N11. This establishes all six nonempty fibres without a new existence assumption.

Let rho be restriction to e,f. The surviving affine signatures are the three affinely independent points `(1,0),(0,1),(1,1)`. Thus rho(L)=Q^2. In any surviving difference combination, requiring zero rho and zero coefficient sum forces the three class coefficient totals individually to vanish. This proves `L intersect ker rho=L0`. Since U has zero rho, the first two dimension identities follow.

The deleted coordinates of A+B+C are (2,2), so beta has zero rho. Its degrees vanish by the same degree count as b. Also `b-beta=A+B+C-3C0` belongs to L. Hence `b in L+U` iff `beta in L0+U`, proving the eta formula. Including N00 introduces the fourth signature `(0,0)`. Their single affine signature relation is `N-A-B+C`, and within-class N00 differences add V. Rank-nullity gives the last dimension identity and F169. All choices change the stated vectors only by the corresponding within-class or surviving spaces. This completes the proof.

**Implication for route (i).** The deleted coordinates of b alone can **never** separate it from L+U in an admissible expansion: rho(L) is already all of Q^2. This is a proved obstruction to that specific separator method, not a refutation of bridge independence. The early coordinate shortcut is retained as a rejected proposal. The corrected beta accounts for all cross-class offsets and keeps the original CW167 content.

Every identity above is checked on all 636 steps, in the mandatory-first order. For every eta=1 step an explicit rational/integer separator annihilating L+U but not b is retained. For each of the 56 `(1,1,0)` steps, the payload identifies a same-class pair whose difference is outside L, and an exact annihilating weight that witnesses it.

## 3. S169 — facial quadrilaterals recover all but at most one lost direction

**Theorem S169.** Suppose G->H is admissible and the expanded face is exactly the quadrilateral `u-v-y-x-u`. Write `a=ux`, `c'=vy`, `e=uv`, `f=xy`. Then N00 is nonempty and the following are exact bijections:

    N -> N-{a}       from N00 to Pux,
    N -> N-{c'}      from N00 to Pvy,
    N -> N-{a,c'}    from N00 to D11.

In particular, all three within-class spaces equal `V=diff(N00)`, so **U=V**. For every such expansion,

    ell-1 <= t <= ell.

Choose N in N00, C0 surviving, and define

    r=N-C0,     s=1_e+1_f-1_a-1_c',     W=L+V.

Then

    parent HC difference space = W+span{r},
    b = 3r+2s mod W.                                  (S169)

If t=ell, exchange holds. If t=ell-1, then r is nonzero modulo W, and exchange fails **exactly** if `3r+2s in W`. In particular it holds if s is outside the parent HC difference space. If s lies inside that space, let alpha be its unique coefficient modulo W, `s=alpha*r mod W`. Exchange is equivalent to `alpha != -3/2`.

**Proof.** Every N00 cycle avoids e,f, so degree two forces both a,c' and both external terminal edges. Removing a gives a spanning ux path; conversely a spanning ux path cannot contain ux (which would be an isolated completed path), and adding a gives an N00 cycle. The unused degree-two terminals v,y force c'. The vy assertion is identical. Removing both a,c' leaves two paths. In the disk outside the quadrilateral, the crossing terminal pairing is impossible. Of the noncrossing pairings, pairing u with x and v with y would give two cycles when a,c' are restored, so the pairing is u-v and x-y. Conversely, a D11 cover cannot contain a or c', and restoring them gives one N00 cycle. Nonemptiness follows from F169 and the first bijection.

Each map subtracts a fixed vector, hence its difference space is exactly V. The entire parent family is the union of the surviving family and N00, so its difference space is W+span{r}. This gives `ell-t in {0,1}`. Choosing the three new representatives from the same N gives

    b=(N-a)+(N-c')+(N-a-c')+2e+2f-3C0=3r+2s.

Other choices change b by W. All remaining assertions follow by taking the quotient by W. No affine-fullness assumption on G is used.

This proves route (ii) for **every facial quadrilateral expansion**, but not for longer faces. The exact remaining obstruction in the equality case is the particular quotient coefficient -3/2, rather than an unspecified extra dimension. It is not proved that this coefficient is universally impossible.

There are 206 quadrilateral steps in the specified census: 12 with `(0,0,0)`, 127 with `(1,0,1)`, 12 with `(1,1,0)`, 32 with `(3,2,1)`, 13 with `(5,4,1)`, and ten with `(7,6,1)`. All bijections and quotient identities pass. Among the 182 with t=ell-1, the observed alpha values are `-1/2` (72), `-3/4` (20), `-5/6` (28), `-7/8` (62). These values are finite evidence only outside the prism theorem below.

The first exploratory coefficient scan used only denominators 1,2,3 and therefore returned empty lists in cases needing denominators 4,6,8. This was an incomplete search, not a negative mathematical assertion; its source/output are preserved. The next exact nullspace calculation recovered all coefficients and is also retained.

## 4. P169 — exchange for every side-face expansion of an even prism

**Theorem P169.** Let `G=C_L square K2`, L even and L>=4, in the usual prism embedding. Expand either opposite-edge pair of any lateral quadrilateral. Then the expansion is admissible and

    d(H)=d(G)+2=L+3.

If the deleted pair consists of the two horizontal rails, `(ell,t,eta)=(1,0,1)`. If it consists of the adjacent rungs, `(ell,t,eta)=(L-3,L-4,1)`. Thus bridge independence holds in both cases for every even L. In both cases the S169 coefficient is

    alpha=-(L-3)/(L-2),
    3+2alpha=L/(L-2)>0.                               (P169)

**Proof.** Use D168's independently proved affinely independent basis of cycles C_0,...,C_(L-1),X,Y. Number top edges t_i, bottom edges b_i and rungs r_i. Focus on the square with horizontal edges t_0,b_0 and rungs r_0,r_1. Direct edge-coordinate comparison gives the affine-difference identity

    (L-2)(r_0+r_1-t_0-b_0)
       = (L-3)C_0 - sum_{j!=0} C_j + X+Y.             (1)

The right-hand coefficients sum to zero. At a horizontal edge i it equals `-(L-2)` for i=0 and zero otherwise. At a rung i, ordinary cycles contribute from C_i and C_(i-1), and X,Y each contribute one, giving L-2 exactly at i=0,1 and zero elsewhere. This proves (1) for every L.

For deletion of r_0,r_1, the surviving cycles are exactly `C_(L-1),C_0,C_1,X,Y`. The N00 family consists of the other L-3 ordinary cycles. Affine independence yields `dim L=4` and `dim(L+V)=4+(L-4)=L`, whereas d(G)=L+1. Thus ell=L-3 and t=L-4. Modulo W, all N00 cycles have the same displacement r from any surviving reference. Summing their coefficients in (1) gives `s=-(L-3)/(L-2)*r mod W`. By S169 and the positive displayed bridge coefficient, eta=1.

For deletion of t_0,b_0, the only N00 cycle is C_0. All other cycles survive, so `dim L=L`, V=0, ell=1, t=0. The square vector s is the negative of that in (1); the coefficient of C_0 in the negated identity is again `-(L-3)/(L-2)`. Hence eta=1 here as well. Rotations and layer exchange cover every lateral face and either labeling.

For completeness, the expansions are cubic, simple and bipartite by their explicit four new vertices and alternating arms; drawing the new square inside the face gives planarity. To see 3-connectivity, deleting two old vertices preserves connectivity of the parent; surviving parent edges are replaced by connected routes through the intact square. Deleting two new vertices leaves all old vertices connected because deleting the two parent edges cannot disconnect a 3-edge-connected graph; each remaining new vertex has its old arm. With one old and one new vertex deleted, the three remaining square vertices form a connected path. If the old vertex was a terminal, only the other deleted parent edge remains relevant, and the connected parent with that vertex deleted has no bridge. If it was not a terminal, any component created by deleting both parent edges in the 2-connected parent-minus-vertex must meet at least two of the four terminals. The path attaches to three of the terminals and consequently joins every such component. These arguments also cover fewer than two deletions. Thus the children are in B.

S169 and R168 finish the rank assertion. The proof uses no bounded-transfer or typed-fullness premise. Independent two-enumerator/two-rank tests check both types for L=4,6,...,18, reaching loss 15 and within-class recovery 14 at order 40 in the child. These are additional finite checks of an analytic infinite-family result; they are not a general graph census. The ten original nine-direction cases have the same tested coefficient -7/8; no unverified graph-isomorphism claim is required to use those checks.

## 5. What distinguishes the two one-loss cases?

Here is an exact functional characterization for arbitrary admissible expansions with ell=1. Let `L^perp` denote all edge weights constant on the surviving family. Then t=0 exactly when every such weight is separately constant on each of Pux,Pvy,D11. Equivalently, every within-new-class difference belongs to L. If that condition fails, t>=1, so exchange holds without requiring the bridge. This follows directly from annihilator duality, independently of graph enumeration. It characterizes the actual structural linear constraint; it does not replace the open inequality by a claimed combinatorial classification.

For facial quadrilaterals there is a sharper parent-cycle description, by S169: t=0 precisely when the entire N00 family lies in a single coset of L; otherwise t=1. Thus the distinction is whether two lost parent cycles already have a difference outside the surviving direction space. Under the additional hypothesis that the parent is affine-full, the t=1 case has W=ker A_G, hence eta=0 automatically. If t=0, bridge independence still requires the S169 coefficient test. For all sample parents the fullness hypothesis is independently checked by d(G)=n/2+1.

All 56 observed `(1,1,0)` steps have explicit new-class pairs recovering the missing direction in `attack-attempt-01.json`; 12 of these are facial quadrilateral steps. The other 44 have face lengths 6 (38) and 8 (6), so being a longer face is **not** an exact discriminator. Conversely, 127 quadrilateral steps have `(1,0,1)`. Among the 441 one-loss **labelled steps** in this sample, bridge-only recovery occurs 385/441 (about 87.3%) and within-class recovery 56/441 (about 12.7%). There is no specified probability measure or topology on admissible graph expansions, so an unrestricted mathematical claim that either case is “generic” is not defined or established. These sample frequencies should not be extrapolated.

## 6. Replay, retained attempts, dependencies and limits

The experiment directory is `frontier/experiments/i169_bridge_independence/`; the receipt/source directory is `frontier/sources/i169_bridge_independence/`.

Authoritative diagnostics are `toolkit.py`, `audit.py`, `support.py`, `attack.py`; successful payloads are `audit-attempt-02.json`, `support-attempt-02.json`, and `attack-attempt-01.json`. The earlier successful support payload is identical, with its original source preserved; support version 2 adds explicit retract bipartiteness/simplicity checks. Both successful explorations are replayed too. The failed first factor implementation and traceback, incomplete coefficient scan, and rejected coordinate-only separator are retained; no failed run or mathematical counterexample was deleted. There were no timed-out runs or blocked retrievals in this iteration.

`verify.py` binds the final report, every owned non-control byte, and every non-context external input **before** running diagnostics. Inventory and successful prevalidation bytes are bound by an exclusively created `seal.json`, whose externally supplied hash closes the control-file chain. The seal is created exactly once after successful `--prevalidate`; it is never resealed. The manifest cannot contain its own hash or the later seal's hash; these control relationships are explicit, not unbound mathematical inputs.

Replay uses `python3 -I -B` and only standard-library Python. A read-only audit hook rejects writes and filesystem mutation, network, process creation, and compile/exec outside owned code and the trusted standard library. Owned source compilation must match the pre-bound source bytes. Guard probes demonstrate rejection before diagnostics. The verifier then requires byte-for-byte equality of deterministic diagnostic JSON, including the successful explorations. The runtime and final hashes are returned separately, avoiding post-seal report changes.

`frontier/TEN-FINDINGS.md` and `frontier/iterations/README.md` are hashed in `external-bindings.json` but explicitly listed as context-only exclusions in `replay-policy.json`; the parent may edit them concurrently. Their changes generate drift receipts, not mathematical exemptions. Python's standard library is the trusted runtime, not a repository dependency. No non-context graph, manuscript, ancestor payload, report, or owned diagnostic byte is exempted. The verifier emits any new context drift read-only.

The literature receipts preserve the search queries and inspected primary abstract/publisher pages: [Gorsky–Steiner–Wiederrecht](https://arxiv.org/abs/2202.11641) and [Björklund–Kaski–Nederlof](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2024.26). Those pages discuss brace reductions and algorithms for another Hamiltonian cycle, respectively; neither inspected page supplied the needed affine-rank theorem. No external theorem from these searches is used. Search is not novelty certification. The pinned catalogue's family 180 has one manuscript; its actual corollary, rather than just its catalogue summary, is the stipulated source dependency.

The 636 original steps have parent order at most 20 and child order at most 24, and are not 636 distinct children. The prism theorem has an analytic proof for every even L; its new finite validation stops at L=18. No finite rank observation proves universal exchange. The square-face argument does not cover the 430 longer-face steps as a theorem, even though they all pass numerically. Nothing here assumes that bounded dual-shore transfers span, or that typed degree-and-port equations are complete.

## 7. Exact claim status and next action

**Proved:** R168/E168, D168 and M168 pass independent audit in their original mathematical scope. F169 gives universal six-class nonemptiness and the exact deleted-edge-free rank comparison. S169 proves `ell-1 <= t <= ell` for every facial quadrilateral expansion and identifies its sole possible equality-case bridge cancellation as `alpha=-3/2`. P169 proves exchange for every lateral-face expansion of every even prism, with bridge coefficient `L/(L-2)>0` and unbounded losses `ell=L-3` for adjacent-rung deletion. The deleted-coordinate-only separator proposal is refuted as a method.

**Finite evidence:** all 636 rank decompositions, the histogram, both mandatory sets, parent-direction containment, explicit separating/recovery weights, the 206 square-face quotient checks, and the bounded computational tests of the two analytic prism theorems. Observed sample frequencies do not define a universal generic case.

**Open:** universal `t+eta>=ell`, hence the general C4 exchange step, (T), and Q164. No counterexample is certified. For quadrilateral expansions the remaining gap is to rule out `s=-3r/2 mod (L+diff(N00))` when r is nonzero in that quotient. For longer faces, both the lower bound `t>=ell-1` and the necessary bridge independence remain unproved.

**Recommended next action:** work in ker A_K using F169's two explicit offsets c and beta. First seek a positive relation or a structural obstruction excluding the single coefficient -3/2 in S169; the even-prism formula provides an unbounded-loss test family with coefficient approaching -1, not -3/2. Separately extend the exact N00-to-path bijections beyond quadrilateral faces, allowing nonlocal operations and keeping the class offsets. Continue to test index 0 and all ten nine-direction steps first. No further deleted-edge-coordinate, bounded-bidirectional-transfer, or typed-fullness shortcut is justified.
