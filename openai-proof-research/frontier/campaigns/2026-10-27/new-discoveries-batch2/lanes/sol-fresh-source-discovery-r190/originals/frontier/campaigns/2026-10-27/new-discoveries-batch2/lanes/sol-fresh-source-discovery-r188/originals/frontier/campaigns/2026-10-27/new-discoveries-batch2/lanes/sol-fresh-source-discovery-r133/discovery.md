# r133: perfect first Lie algebra — three unresolved full statements

Disposition: no nominee, no complete source proof or refutation, no PROOF.md, Lean or paper. Root alone adjudicates. No count edits. The following are precise source questions, not assertions of new theorems.

## Selection and primary attribution

The lightweight first scan searched original SUMMARY/discovery/PROOF/review/DECISION filename roles for numerical-semigroup/Ciolan/Moree and then Burde/Dekimpe/Monadjem/post-Lie identifiers. Numerical-semigroup sources were already heavily screened (notably r71 and r110); they were abandoned before paper downloading. The original r71 unrestricted AP pseudo-Frobenius/minors obstruction and r110 dominance-defect gap were read, rather than treating a keyword as a global exclusion. The new pool is finite-dimensional complex Lie algebras and their post-Lie structures. No exact previous attempt on the selected paper was found. This is a bounded project-history observation, not literature novelty evidence.

Primary: Dietrich Burde, Karel Dekimpe, Mina Monadjem, *Post-Lie algebra structures for perfect Lie algebras*, Communications in Algebra 52(10) (2024), 4255–4267, DOI 10.1080/00927872.2024.2344638; arXiv:2311.08985v1, submitted 15 November 2023. Current arXiv page observed 29 October 2026 lists v1 only. The author PDF dated 8 March 2024 and actual published article at PMC11304516 were obtained. The introduction's three conjectural cases, Definition 2.5, Propositions 2.6–2.7, 3.1–3.4, 3.11–3.12, Theorem 3.10 and its complete kernel-case proof, and final Theorem 5.1 were read. PDF locators below refer to the 15-page author PDF; published numbering was checked in the full article, not inferred from the abstract.

For all three targets, V is an arbitrary nonzero finite-dimensional complex vector space; g=(V,[,]) is perfect, [g,g]=g, and non-semisimple. The second bracket n=(V,{,}) has the same V. A structure is an arbitrary complex bilinear product x·y satisfying, for EVERY x,y,z in V,

1. x·y−y·x=[x,y]−{x,y};
2. [x,y]·z=x·(y·z)−y·(x·z);
3. x·{y,z}={x·y,z}+{y,x·z}.

The source introduction p1 conjectures nonexistence in these three cases; Section 3 p5 fixes the complex field. Table 5.1 pp13–14 still has question marks. No completeness or global integrability assumption is present.

**N (strongest investment):** for EVERY such g and EVERY nilpotent nonabelian n, there is no such product. Arbitrarily high dimension and nilpotency class are included. No restriction on the Levi factor or radical of g may be added. This also addresses the negative answer to Burde–Dekimpe 2016 Question 3.5 for the non-semisimple complex case; that original question has broader perfect/characteristic-zero wording, which is not silently claimed here.

**S:** for EVERY such g and EVERY simple complex n, there is no such product. Source Theorem 3.10 only closes n=sl3(C), and sl2(C) is vacuous by dimension. All other simple types/ranks remain in scope.

**SS:** for EVERY such g and EVERY semisimple non-simple complex n, there is no such product. Source Proposition 3.12 closes n=sl2(C)⊕sl2(C); Proposition 3.11 closes the special g=s⋉V with s simple and V irreducible abelian. Arbitrary multiple Levi factors, reducible radicals, nonabelian radicals and unbounded dimensions cannot be suppressed. S and SS share the same mechanism; they are not nominated as separate credits.

## Closest bodies and an apparent 2026 shortcut

Burde–Dekimpe, *Post-Lie algebra structures on pairs of Lie algebras*, arXiv:1505.00955, actual Section 3 pp4–6: Proposition 3.3 already gives no structures for perfect g and n abelian or class at most two, Question 3.5 asks about nilpotent n, and Proposition 3.6 proves the five-dimensional sl2⋉V(2) case, using the derivation algebra and a free class-three exceptional case. The new source Proposition 3.2 pp5–6 extends to the two six-dimensional perfect non-semisimple g; its argument uses classification in dimension nine. Neither proof is an arbitrary-dimension theorem. Reproving any of these cases is uncredited.

Marco Damele–Andrea Loi, *Structural and rigidity properties of Lie skew braces*, arXiv:2507.06214v3, last revised 25 February 2026 (latest observed; v2 summaries were not substituted), published J. Algebra 695 (2026), 356–383, DOI 10.1016/j.jalgebra.2026.01.048: read introduction pp2–4, Definition 2.10/Remark 3 and examples pp8–9, and actual Theorem 1.1 proof pp13–14. The source's group convention puts the second-bracket algebra g of our notation in its circle slot. Theorem 1.1(S2) proves solvability transfer for connected GLOBAL Lie skew braces, using a common global Euclidean manifold, Levi decomposition, and linearity. Page3 explicitly leaves the nilpotent/perfect post-Lie algebra question undecided and says such an algebra would be nonintegrable. An arbitrary infinitesimal post-Lie product cannot be declared a global simply transitive action: its local orbit can be open without being all of the nilpotent group. Thus that theorem is not a resolution of N. The semisimple rigidity direction R2 concerns a semisimple FIRST algebra in our convention, the opposite orientation from S/SS. This comparison eliminates a tempting but invalid proof, not a new result.

The 2026 CPA classification search lead concerns COMMUTATIVE products on a single fixed Lie bracket. In our setting g≠n and the skew part of · is prescribed by the difference of brackets; it is not a CPA structure. That lead was not promoted to a subsumer or audited in full. It remains a stated scope limit.

## Sustained full-scope attempt for N

Write A_x(y)={x,y} and L_x(y)=x·y. The axioms give [L_x,L_y]=L_[x,y], each L_x is a derivation of n, and [L_x,A_y]=A_(L_x y). These identities hold in every dimension/class.

1. **Affine graph.** x↦(x,L_x) is a Lie embedding g→n⋊Der(n), since its bracket's translation part is {x,y}+L_xy−L_yx=[x,y]. This is a graph complementary to Der(n) as vector spaces. It yields a local action, not the missing global transitivity. The source already uses this embedding.

2. **Traces.** Perfectness implies tr L_x=0 and tr ad_g x=0: each is a linear functional killing commutators. Nilpotence gives tr A_x=0. Put R_x(y)=y·x; the first axiom says ad_g x=L_x−R_x+A_x. Hence tr R_x=0 for all x. This is necessary but does not prove nilpotence of every R_x, global completeness, or solvability of g. The standard pre-Lie completeness criterion cannot be applied before a pre-Lie product exists. No asserted post-Lie completeness theorem with exactly these hypotheses was found/read.

3. **Exact class-two reduction and its failure beyond.** Let D_x=L_x+(1/2)A_x. Its product has commutator [x,y]. Direct expansion, using the derivation identities, gives

    [D_x,D_y]−D_[x,y] = −(1/4) A_{ {x,y} }.

Indeed the two cross terms sum to (1/2)A_(L_xy−L_yx), the inner-inner term is (1/4)A_{ {x,y} }, and the subtracted term is (1/2)A_[x,y]; substituting PA1 leaves the displayed coefficient. Thus D is pre-Lie iff {{n,n},n}=0. This recovers precisely the already-public class-two route. Nilpotence alone does not zero that curvature.

The exact diagnostic uses the free class-three nilpotent n on e1,e2, with {e1,e2}=e3, {e1,e3}=e4, {e2,e3}=e5. Taking g=n and L=0 is a genuine post-Lie structure. For x=e1,y=e2,z=e1 the defect is +e4/4. Its lower central dimensions are 5,3,2,0. The checker verifies Jacobi and the curvature identity on all125 ordered basis triples with rational arithmetic. This g is NOT perfect: it is an obstruction only to the unconditional flattening step, never a counterexample to N.

4. **The actual nonlinear missing bridge.** Any further pre-Lie product with the same bracket would have the form D_x y+B(x,y), with B symmetric bilinear. A sufficient full-scope construction would solve, for all x,y,

    [D_x,B_y]+[B_x,D_y]+[B_x,B_y]−B_[x,y]
      = +(1/4)A_{ {x,y} }.

No solution is constructed. Although the right side is filtration-lowering for the lower central series of n, D is not initially a representation; invoking ordinary Whitehead cohomology for D is invalid. Moreover perfect g need not be semisimple. Nilpotent triangularity by itself does not solve this Maurer–Cartan equation. A central-quotient induction also needs the quotient to carry BOTH brackets and products. Characteristicity of n^k gives L_x(n^k)⊆n^k, but does not give L_y x∈n^k for y∈n^k; the latter appears in [x,y]. Thus n^k need not be treated as a g ideal without an additional argument. Neither the trace route nor the quotient route closes the missing step.

This is a full-scope attempted reduction with explicit obstruction, not a proof outline presented as complete. The strongest source falsifier would be exact structure constants of a nilpotent n and perfect non-semisimple g satisfying all three PA identities. No such witness was obtained. The strongest objection to claiming progress is that all closed steps are classical/source machinery; only the hard universal step remains.

## S/SS: exact all-rank reduction and gap

For semisimple n, Der(n)=ad(n) and Z(n)=0. There is therefore a unique linear R with L_x=ad(Rx). PA1 gives [x,y]={Rx,y}+{x,Ry}+{x,y}, and PA2 says R is a weight-one Rota–Baxter operator. The two maps j1=R+I and j2=R from g to n are Lie homomorphisms and j1−j2=I. Conversely the transverse pair-of-homomorphisms construction gives a post-Lie product; this is precisely source Proposition 2.6, not a novel reduction.

Any full proof of S/SS must rule out every perfect non-semisimple g of dimension dim n with such a transverse pair. Both kernels are nonzero (an injective homomorphism in equal dimension would identify g and n) and their intersection is zero. Proposition 3.11 succeeds when every nonzero ideal contains a single irreducible radical V. A general perfect g can have disjoint nonzero ideals, so that argument is not universal. Perfect images in n cannot simply be declared semisimple: the derived maximal parabolic sl2(C)⋉C² embeds as a perfect non-semisimple subalgebra of sl3(C). Theorem 3.10 handles that small-rank situation using explicit kernel cases and bounds on abelian subalgebras; its final paragraph explicitly says the generalization is unclear. No uniform kernel/ideal obstruction for arbitrary simple type or arbitrary semisimple direct sums was proved here. A transverse pair j1,j2 with g perfect non-semisimple is an exact falsifier for S/SS; none was found.

## Historical and registry limits

The subsequent all-date screen, before the sustained derivation above, hashes 426515 selected text paths into278029 distinct SHA256 bodies. All aliases are retained in compressed JSONL; 45 matching distinct bodies were reopened with unchanged hashes and all matching excerpts saved. Four numeric substring collisions on2344638 are removed by digit boundaries in the secondary pass. The remaining41 matches are registry tree/blob-path metadata or copied excerpts pointing to the Ari free-word work; there is no matching original attempted disposition on2311.08985. No global hit cutoff was used. The initial 8-excerpt display limit is superseded by all matching excerpts in original-reopen-receipts.json. Forty-one original science-role r111–r113 paths are explicitly retained. No entire r111–r113 lane was omitted.

Each shard receipt lists oversized paths above12MB, binary/NUL files, extensions omitted and generated-cache-role skips. Included formats are md/txt/json/jsonl/py/sh/lean/tex/csv/tsv/html/htm/yaml/yml/toml/bib/rst/log. PDFs, archives, notebook/binary and other omitted formats are not claimed text-screened; unextracted mathematics may remain. Role skips can omit retrieval echoes but are not semantic clearance. The snapshot is as-read, not transactional. Lexical absence cannot exclude aliases absent from the chosen pattern or semantic equivalents. The own lane is excluded.

At23:09:59UTC on29October2026, the one Omega default HEAD observation is e1ff281c3881e633b86be1072f049a778bdbdc1b. Fixed2108cd1f896d198a2137f61fdbad1cd72d660b18→e1ff compare has14commits/15paths, merge-base exactly2108, below250/300 response caps. Paths cover periodic-orbit orders, Seidel spectral gap, and qutrit entanglement. This is not generic semantic clearance. OpenAI current HEAD remains7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a. Do not substitute Omega main.

The inherited r3 eleven-interval205commit279body and r4 fixed28commit538path receipts and subsequent historical notes are context, not a freshly completed semantic screen for these new Lie targets. Actual current pinned Omega AriProjection, AriWordOperations, AriWordProduct, AriCoproductFiltration blueprint theorem bodies and Library/LieTheory/burmesterkuhn2025postlie.md were fetched. They concern Burmester–Kühn2504.19661 Conjecture4.29, rational free words and the ari right-factor filtration, not our finite-dimensional perfect/nilpotent or perfect/semisimple nonexistence assertions. These displayed theorem bodies are not an independent Lean proof replay. No universal registry/literature clearance, exhaustive specialist database audit, or worldwide priority is asserted.

No access-control challenge was bypassed. The web-tool author-papers landing page failed once and was not retried; the already successful direct public author PDF was retrieved once more by the guarded receipt utility solely to bind HTTP metadata/hash (same bytes), not to evade an access restriction. No account, browser tab, post, upload, external message, git operation or shared edit occurred.
