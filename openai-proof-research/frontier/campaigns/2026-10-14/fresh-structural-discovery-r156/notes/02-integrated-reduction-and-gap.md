# r156 — integrated subgroup-poset calculation

**PREFREEZE / no nominee.** No theorem was frozen and no author-proof nominee is submitted. No independent correctness, contribution, acceptance or count is assigned. These are derivation notes and a strongest-input comparison. The first catalogue family (Ehrhart/lattice-polytope algebra) yielded no entry; the second and only developed family is Source310 subgroup-poset topology. No new family was added after these screens.

## 1. Actual source and primary contracts

Source310, `Rational-homology-and-Quillens-conjecture-September-24-2026`, at the stipulated pin has `thm:main`: for every finite group G and prime p, O_p(G)=1 implies nonzero augmented reduced rational homology of A_p(G). The empty poset has Htilde_-1=Q. The introduction already gives the every-field consequence. Its operative statements/proofs are stipulated true; the reading here is to understand usable operations, not audit that premise.

The source's `lem:saturated-residue`, `lem:product-shuffle`, `lem:propagation`, `cor:maximal-family`, and `lem:restriction` were read with their complete proofs. The last restricts full-flag cycles at a maximal intersection index via a fixed complement, not by arbitrary intersection of all flags. Decorations explicitly require injectivity of actual coefficient data. These operations are credited rather than offered as new work.

Thévenaz–Webb, *Homotopy equivalence of posets with a group action*, author PDF, Theorems1–2, Proposition1.7 and Lemma2.1, supplies the equivariant fiber theorem, ordered deletion and elementary/radical equivalences with actual proofs. In particular it does not say that the intersection of the two collections has the same homotopy type. Its Lemma2.1(ii) characterizes **equivariant contractibility** of the upper interval, not ordinary rational acyclicity without the source input.

Gelvin–Møller, arXiv1301.0193v2, `lemma:boucEI2`, `lemma:(1,P)contract`, `thm:SG`, gives the strongest directly compatible slice/coslice proof used here. Its `rmk:BoucInterpretation` explicitly warns that the union of the two classes of deletable objects cannot generally be discarded. The actual upper-interval equivalence is Q -> N_Q(P)/P, already credited there to Quillen1978 Lemma6.1. Thus neither the normalizer retraction nor the warning below is new.

Bouc1984, pp49–52, was read from all four rendered pages. Proposition4 and its corollary give the deletion result; Proposition9 provides the classical building basis indexed by upper unitriangular matrices, of cardinality p^{binom(d,2)}. This short note largely states results rather than supplying their full proofs. The actual deletion proof was read in Thévenaz–Webb and Gelvin–Møller. Original Quillen1978 acquisition failed; that original was not freshly read.

Piterman arXiv2003.06384v2, lines463–775, contains actual inflation/centralizer-attachment, full-chain and shuffle proofs, including `generalizedHomologyPropgation`. Its coefficient extraction already works for arbitrary centralizer classes, not just one specially chosen representative. Its relaxed proper-subposet framework is compatible with the source's deletion. The Aschbacher–Smith original was not acquired/read, so no complete transitive bibliography claim is made.

Arithmetic-r44's original `screen310.md` was read in full. It already identifies coefficient changes and Symonds/semisimplicity bounds as paid, and records a many-frame ambient-rank question. That question is not renamed here. Symonds1998 was freshly read in full text, with its p402 diagram viewed; the quotient and relative statements remain credited.

## 2. Local homology at every nonempty subgroup flag: paid composition

Put X=S_p(G), the nonidentity p-subgroups of a finite group. Homology is augmented. For a nonempty flag sigma=(P_0<...<P_k), the link is the join

  (1,P_0) * (P_0,P_1) * ... * (P_{k-1},P_k) * X_{>P_k}.               (1)

Here each middle interval is in the subgroup lattice of the p-group at its right endpoint.

The normalizer condition gives P<N_Q(P) for P<Q, so Q -> N_Q(P) retracts X_{>P} downwards onto the subposet of overgroups in which P is normal. Quotienting by P identifies that subposet with S_p(N_G(P)/P). This equivalence is already Quillen/Gelvin–Møller, with no elementary-lift assumption.

For (H,K), if H is not normal in K, the same map retracts the interval to (H,N_K(H)], which has a maximum strictly below K and is contractible. If H is normal, the interval is the proper nonzero subgroup poset of K/H. If its Frattini subgroup is nontrivial, Q -> Q Phi(K/H) -> Phi(K/H) contracts it; a proper Q stays proper by the nongenerator property. Otherwise K/H is elementary abelian and the interval is its subspace building. The first interval in (1) is the H=1 instance. These are classical p-group operations.

Consequently a contractible join factor occurs unless P_0 is elementary abelian and every P_{i-1} is normal in P_i with elementary abelian quotient. If these conditions hold, set

  d_0=log_p|P_0|, d_i=log_p|P_i:P_{i-1}|,
  a=sum_i d_i=log_p|P_k|, M=p^{sum_i binom(d_i,2)}.

Building homology and join Künneth give, as rational vector spaces,

  Htilde_j(link sigma) ≅ Q^M tensor
      Htilde_{j-a+k+1}(S_p(N_G(P_k)/P_k)).                            (2)

For x in the relative interior of sigma, the local homology is

  H_i(|X|,|X|-{x};Q) ≅ Q^M tensor
      Htilde_{i-a}(S_p(N_G(P_k)/P_k)).                                (3)

All d_i=1 and empty-upper-interval cases use degree -1, not an ordinary non-augmented convention. Formula(3) follows from the k-simplex interior shift k+1. It is an assertion about the particular Brown-complex realization; global homotopy equivalences to Quillen/Bouc complexes need not preserve pointwise local homology.

O_p(N_G(P)/P)=1 exactly when O_p(N_G(P))=P. If it is nontrivial the upper interval contracts. If it is trivial, stipulated Source310 and the primary elementary/all-subgroup equivalence give nonzero augmented homology. Therefore nonzero local rational homology in some degree is characterized by the elementary-section conditions and radicality of the top subgroup. This is the full all-flag source/classical composition, not a restricted nominee or a substantial contribution claim. No equivariant representation or integral-torsion refinement of (2) is asserted without its additional bookkeeping.

## 3. Both reductions can be combined, but not by intersection

The simplest attempted model retains only A_p(G) intersect B_p(G). It fails already for GL_3(F_2). Direct exact enumeration gives:

- Brown poset:77 vertices,231 edges,147 triangles; reduced Betti polynomial8t.
- Quillen poset and Bouc poset:each35 vertices and42 edges; reduced Betti polynomial8t.
- Their intersection:14 incomparable Klein-four subgroups; reduced Betti polynomial13.

This is not a universal obstruction theorem. Gelvin–Møller already warns against the attempted union of deletions. More importantly, the **compatible** replacement is paid by the existing fiber/deletion machinery:

  D={(E,R): E in A_p(G), R in B_p(G), E<=R},

with componentwise order. Projection to B has lower fiber over R retracting by (E,R') -> (E,R) onto A_p(R), which contracts via the characteristic central elementary subgroup Omega_1 Z(R). Projection to A has upper fiber over E retracting by (E',R) -> (E,R) onto B_{>=E}. To see B_{>=E} contractible, start with the cone S_{>=E} and delete nonradical objects in increasing inclusion order, so their upper intervals are still the original ones; the primary contraction stays above E. The same contractions are equivariant under the relevant stabilizers. The equivariant fiber theorem thus supplies both equivalences.

In the finite diagnostic D has203 vertices,504 edges,294 triangles and Betti polynomial8t, as expected. Its being larger in this example is not a complexity impossibility claim. No missing simultaneous-comparison theorem is parked as a discovery: the pair-incidence comparison above already pays it.

## 4. Keep the global differential, not just the local dimensions

Filter S_p(G) by subgroup order p^a. Each new vertex P contributes the cone on its lower interval. The first relative homology page has a contribution only for elementary P, in total degree a-1. That contribution is its Steinberg module St(P)=Htilde_{a-2}((1,P)). Therefore this standard filtration has only one diagonal, and its remaining differential goes between consecutive ranks. The resulting augmented complex has

  C_{a-1}=direct_sum_{E elementary, rank E=a} St(E), C_-1=Q,

with differential given by deleting the top subgroup and collecting residues on elementary codimension-one subgroups. It computes the Brown/Quillen homology. This is the usual filtered-chain/Whitney-homology construction, not a new algorithm. Spectral-sequence concentration does **not** remove its d1 differential.

For GL_3(F_2) the complex is Q^28 -> Q^21 -> Q, with differential ranks20 and1. Thus H1 has dimension8. A direct basis for each rank-two summand is [L]-[L_0] for the other two lines L of E; the corresponding boundary columns are literal differences of order-two subgroup vertices. This pays a complete concrete connecting-map computation, not only a failed naive route.

## 5. Source propagation pays more than a single surviving class

The source's exact propagation hypotheses retain a faithful configuration A, H=LA, r=rank A, K=C_G(H), no qualifying larger faithful configuration, the centralizer condition(i), and its deleted poset X. Keep **all** of these hypotheses. Let Z be the rational space of degree r-1 cycles in A_p(H), and let V_A be its image on full flags ending at A. A source cycle ensures V_A is nonzero, but its dimension need not equal the full frame parameter dimension.

Choose a linear section s:V_A -> Z of this coefficient projection. For every b in the augmented chains of A_p(K), set

  I(v tensor b)=s(v) boxtimes b.

Exactly the source support argument puts I in C_*(X). Collect q_* R_sigma over all full flags sigma ending at A, where q(E)=C_E(L) is the source retraction on X_{>A}. The source coefficient identity holds for EVERY b, so this collection sends I(v tensor b) to v tensor b. A linear projection of the full flag-coordinate space onto V_A makes a left inverse on all chains. With the usual shifted differential (-1)^r, these are chain maps. Consequently V_A tensor Htilde_b(A_p(K)) is a split summand of Htilde_{r+b}(X), and hence of the ambient homology under the source homotopy equivalence.

The splitting can also respect T=N_G(L) intersect N_G(A): Z and V_A are T-modules, all flags ending at A are permuted, and the source deletion and q are T-equivariant. Over Q choose s and the coordinate projection equivariantly by averaging. This produces the corresponding T-module splitting. It is still the source maps plus rational linear algebra. No new source-frame construction, integral division, or G-induced independence is being smuggled into this calculation.

Thus an alleged gap about transporting **all centralizer classes** or **independent same-top coefficient images** would be false after strongest composition. The actual residual compatibility question concerns different top groups, their different deletion posets and the relations among their images. It is already adjacent to arithmetic-r44's recorded many-frame issue; no new gap is claimed.

The finite example makes this distinction exact. The global degree-one cycle space has dimension8. Its restriction to the three full flags at EACH of14 top Klein-four groups has rank2. The sum of the individual ranks is28, whereas the joint restriction rank is8. All455 nonempty Brown flag links also agree with (2). These computations rule out simply adding local dimensions; they do not rule out a new compatible construction or furnish one.

## 6. Ending boundary

The paid reduction includes the full local link description, both compatible poset reductions, the actual global Steinberg differential, and the full same-top/centralizer split propagation. Source decorations, maximal-index restriction and original propagation remain available at their full stated scopes. Coefficient changes and the Symonds isotypic bound are credited and not resubmitted.

No new uniform control of the relations among distinct top-group residue images or of the resulting connecting-map ranks was proved after these operations. No exact stronger all-group conclusion with a complete proof and identifiable nonroutine operation emerged. That is the unpaid research boundary, not a frozen theorem, substantial obstruction, novel conjecture, or priority claim. A class-specific matrix calculation, a conditional splitting hypothesis, the source consequence(3), and a renamed r44 rank question are all declined as nominees. No old frozen target or disposition is changed.
