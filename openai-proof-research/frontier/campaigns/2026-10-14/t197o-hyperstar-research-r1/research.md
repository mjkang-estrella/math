# H2 research outcome: unresolved; exact mechanism obstructions

This is an auxiliary research packet, not a theorem nomination or an independent review. The all-odd-prime target T197O and the H2 finite-matching existence statement remain distinct. This packet does not prove H2 and does not assert it is false. The main author's separate companion-based proof of T197O is outside this packet's claimed deductions.

The frozen interface is `private/context/hyperstar-interface.md`, SHA256 `b2f6064d2710b3a994a38525a8a4a54a5297bd44c20c5dfb053bfea75bfe2809`. Its entire text and frozen scope were read before the work below. All pinned OpenAI source theorems are accepted as stipulated. No upstream truth audit was performed.

## 1. Exact scope and notation

Fix any odd prime p. Put q=p^4, v=q^2+q+1, e=p^2+p+1, and E=(p−1)e=p^3−1. The ordinary sockets are the v points of PG(2,q); the E extra sockets form p−1 disjoint copies of the points of PG(2,p). The outer-vertex types, exceptional A root, and balanced counts are exactly H1. A socket class contains p sockets. On each side Y, each socket occurs N_Y times and each class has N_Y centres. Edges go from outer vertices to centres and have positive labels t in the free rose on the sockets.

H2 asks for some sufficiently large m=1 mod p^2 and some matching choices such that no other outer vertex in the chosen B root component has identity root-path label in the cone group G. No claim for only p=3 or sufficiently large p would settle that statement. No change of finite types is proposed here.

## 2. Regrouping cannot restore the squared-word contraction

**Proposition 1.** Keep H1's socket set and types. For every partition of the sockets into p-element classes, the ordinary, all-ordinary-class part of the limiting squared-turn matrix has spectral radius strictly greater than one. In particular, regrouping sockets alone cannot recover the unchanged source197 squared-word argument, even with a nonconstant positive weighting vector.

**Proof.** Let O be the set of ordinary sockets in classes containing no extra socket, and put o=|O|. A class containing an extra socket contains at most p−1 ordinary sockets. There are at most E such classes. Therefore

    o ≥ v−(p−1)E = p^8+p^3+p =: o_min.

Every class contained in O has size p. In a path, an incoming ordinary socket a at a centre has p−1 distinct outgoing possibilities b in its class. At the ensuing outer vertex, any different ordinary socket c has limiting turn weight 1/(q+1), because two distinct ordinary points lie on exactly one line. Restrict c to O. The squared matrix for this centre turn followed by this outer turn is

    K[a,c] = #{b in class(a)\{a}: b≠c}/(q+1)^2.

Every row sums to

    R_o = (p−1)(o−1)/(q+1)^2.

Thus the all-ones vector is an eigenvector. Nonnegativity and the maximum-row-sum bound give rho(K)=R_o. For all p≥3,

    (p−1)(o_min−1) ≥ 2(p^8+p^3+p−1) > 2p^8,
    (q+1)^2 = p^8+2p^4+1 < 2p^8.

The last inequality holds since p^4≥81 and (p^4−1)^2>2. Consequently R_o>1. All k-step restricted squared masses grow exactly by R_o^k when summed against the all-ones vector. Other sockets and words only add nonnegative mass.

For completeness, write o=kp. The matrix is

    K=((p−1)J−diag(J_p,...,J_p)+I)/(q+1)^2.

Its eigenvalues are R_o once, −(p−1)/(q+1)^2 with multiplicity k−1, and 1/(q+1)^2 with multiplicity k(p−1). Hence no positive vector f and lambda<1 can satisfy Kf≤lambda f: that would imply rho(K)≤lambda. There are finitely many entries for each fixed p; O(1/m) changes caused by type rounding cannot remove the strict spectral gap. ∎

The integer numerator of the minimal gap is

    (p−1)(p^8+p^3+p−1)−(p^4+1)^2
      = p^9−2p^8−p^4−p^3+p^2−2p.

For p=3 it equals 6456, and R_min=3295/1681. These are exact diagnostics, not a numerical existence argument.

This proposition extends H4's specified grouping obstruction to **every grouping of the unchanged sockets**. It does not apply to a new probability law with correlated matching choices whose path probabilities no longer factor through these turn weights. It does not exclude a different topological criterion or prove failure of H2.

## 3. Completing a star does not supply a higher moment

**Proposition 2.** In H1's independent matching law, fix one socket class on one side, let its centre set have size N, and let t_1,...,t_k be distinct sockets of that class. Fix outer endpoints x_i carrying t_i. The probability that all k endpoints meet a common, unspecified centre is N^(1−k).

**Proof.** For a fixed centre z, the k independent bijections have probability N^(−k) of sending those endpoints to z. The events for the N different centres are disjoint. Sum over z. This calculation remains true if some outer endpoints coincide, since the socket bijections are different. ∎

In particular, a specified two-socket turn costs N^−1. Conditional on that turn, all remaining arms of its centre already exist uniquely. If their endpoints are left unspecified, summing over their possible endpoints has conditional probability one. There is no additional N^(−(p−2)) factor. That extra factor is available only after fixing p−2 additional endpoints, and the endpoint choices must then be counted.

This rules out one proposed shortcut: enlarging each paired path turn to a complete p-star does not automatically replace the source's square of a word weight by a pth power. Repeated arms and repeated centres must instead be counted as the same underlying prescriptions. This is consistent with the source's image-graph/multiplicity method; it is not a criticism of that method.

## 4. Finite quotients force p-fold B collisions

The following statement uses the unconditional algebraic identities ab=1 and ac=0 from frozen H3; it does not assume H2. Write B' for the finite set of outer vertices of the B root component, h_y for their root-path labels, and

    c = sum_{y in B'} h_y^(-1) in F_p[G].

**Proposition 3.** Let R be the finite residual of G, the intersection of the kernels of all homomorphisms from G to finite groups. For every coset gR, the number of y in B' with h_y in gR is divisible by p. In particular at least p vertices of B' have h_y in R. If H2 holds, at least p−1 nonroot vertices of B' represent nonidentity elements of R.

**Proof.** First take a homomorphism phi:G→Q to a finite group. The induced unital map of group algebras preserves ab=1 and ac=0. The algebra F_p[Q] is finite dimensional, so a one-sided inverse is two-sided: for example, its left-multiplication operators are square matrices, and A B=I implies B A=I. Multiplying the image of ac=0 by the inverse of the image of a gives phi(c)=0. The coefficient of u^−1 in this element is

    #{y in B': phi(h_y)=u} mod p.

Thus every finite-quotient fibre has cardinality divisible by p.

Consider the finitely many distinct images of h_y in G/R. For each pair of different images choose a finite quotient distinguishing them; such a quotient exists by the definition of R. The product of these finitely many quotients is finite and distinguishes all the images simultaneously. Its fibres on B' are exactly the R-coset fibres. They therefore all have cardinality divisible by p. The root has h_root=1, so its fibre is nonempty and has size at least p. Under H2 no other vertex has h_y=1 in G, giving the final assertion. ∎

No finite quotient can isolate the B root among all other B outer vertices. The same obstruction rules out a proof obtained by mapping to a residually finite group while retaining all the required B-root distinctions: finite support permits one finite quotient to retain those distinctions simultaneously. This is a limitation on possible certificates, not an obstruction to H2 itself. No soficity or external direct-finiteness theorem is needed for Proposition 3.

## 5. What the cone topology does and does not transfer

The directed incidence graph is immersed in the free rose: at an outer vertex its outgoing signed labels are distinct positive sockets, and at a centre they are the distinct inverse sockets in its class. Positive and negative letters form a fixed-point-free inverse alphabet. Thus the deterministic cone-picture and band-surgery argument of source197 `topology.tex`, Proposition `prop:cone-criterion`, applies to this incidence graph once its stated arrangement-exclusion hypothesis has been established.

A smaller sufficient condition is enough here: exclude only reduced arrangements having an exceptional boundary that starts at the selected B outer root and ends at a different B outer vertex. If H2 fails, take a null-homotopy of such a path minimizing the total inner and outer boundary length. Tighten the graph paths and remove constant inner boundaries. There must remain an inner cone disk, since a positive immersed graph path labels a nonempty freely reduced word. Pair inverse edge occurrences by arcs in the complementary rose map. If two paired occurrences use the same underlying graph edge, the source's four band surgeries shorten the picture; in the exterior cases they retain the fixed graph endpoints, and in an inner splitting one retains the component with the exterior boundary. Minimality therefore gives a reduced arrangement of precisely this rooted kind. Excluding those arrangements proves H2 without an asphericity or torsion-free conclusion.

This observation supplies no exclusion theorem. The source's probabilistic theorem `thm:no-arrangements` in `planar.tex` uses `thm:bounded-patterns`, which in turn uses `lem:word-decay`. Proposition 1 prevents its unchanged transfer. The source's diameter and short-closure estimates also need separate adaptation to the incidence graph, whose centres have degree p rather than the source's minimum degree 129. They were not silently imported.

The characteristic-two companion's `02a-embedding.tex`, Lemma `lem:embedding`, uses local finite groups and one subgroup label per hyperedge. Its planar balance proof is a different mechanism. In H1 the same socket label is shared across different centres and across A and B; that shared label is essential to H3. Substituting distinct centre labels from the companion does not prove H2 or preserve H3 without a new argument. No such substitution is claimed.

## 6. Attempts, limits, and completion status

The investigation considered regrouping sockets, saturating paired turns to full stars, using finite quotients or deterministic finite-group models to separate the root, and transferring the finite-subgroup planar balance mechanism. Propositions 1–3 make the first three limitations precise. The last mechanism has an unfilled shared-label compatibility step. General correlated matching laws remain possible; no law with a proved rooted-arrangement exclusion was constructed.

No explicit H1 matching pair was constructed or tested. No finite computations are presented as evidence for H2. No all-prime root-protection existence statement, conditional conjecture, or partial-prime substitute is nominated. H2 remains the exact unresolved interface.

Novelty limit: these are elementary mechanism diagnostics relative to the frozen H1–H4 proposal. Proposition 1 strengthens its grouping quantifier; Proposition 3 extracts a finite-residual consequence of its existing algebra. No new-to-literature or substantial-contribution claim is made. The work stopped at the parent's instruction to seal the current exact results after a separate route made H2 unnecessary for the parent's T197O proof.

## 7. Reading and validation boundary

`source-receipts.json` records private copies, pinned raw URLs, Git blob identifiers, SHA256 hashes, byte counts, and exact complete-file reading limits. The complete preprint tree was parsed and the selected source paths checked; the truncated root tree was not used. The following eight sections were read completely:

- October 4 torsion-free F2 paper: `random.tex`, `patterns.tex`, `planar.tex`, `topology.tex`, `assembly.tex`.
- September 26 odd-characteristic companion: `01-introduction.tex` (including the theorem for one specified prime).
- September 23 characteristic-two companion: `01-introduction.tex` and `02a-embedding.tex`.

Other sections of the companions, bibliography entries, external cited papers, and separate figure input files were not read for this packet. Their contents are not used as independent inputs. The source theorem scope and local planar mechanism are all that is claimed from those companion readings. No browser UI, uploads, shared-index changes, git staging, or commits were performed.

`python verify.py` is read-only. It checks the public manifest, all private receipt hashes and Git blobs against the complete tree, the frozen interface hash, the exact polynomial identity for the spectral gap, small exact matrix spectra, and exhaustive small-N star probabilities. These computations validate stated finite diagnostics and provenance; the general proofs above establish the quantified deductions. The final manifest hash is supplied outside the packet in the delivery message.
