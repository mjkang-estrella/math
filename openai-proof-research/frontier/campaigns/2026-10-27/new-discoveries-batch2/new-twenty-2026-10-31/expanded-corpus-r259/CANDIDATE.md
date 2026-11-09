# 364698: complete ordinary proof, qualification hold

Zero credit. No Lean work has been performed. Root must adjudicate significance and complete journal / public-proof clearance before routing implementation. The proof is short; that is not a claim of eligibility.

## Exact source and semantic scope

Johnson–Kaya–Matzke, arXiv:2409.04869v1, Definition 1.2, Theorems 2.1–2.3 and Conjecture 2.1 (pp. 3–6). Vertices of P_n are consecutive integers, and G(P_n,D) joins distinct vertices whose ordinary path distance lies in D, where D is a k-element subset of {1,...,n−1}. Spec(P_n,k) consists of the chromatic numbers of these distance graphs. It is not an adjacency eigenvalue spectrum. The one listed arXiv version is cached in full. Source pages 4–6, including both proofs of Theorem 2.1 and all constructions of Theorems 2.2–2.3, were read. No finite counterexample or source figure is used.

MathDB's two purported older references, arXiv:1412.1438 and 2005.02797, are respectively Tao–Vu's random-matrix simple-spectrum paper and Vu's random-matrix survey. Their actual downloaded titles and bodies do not establish the path-spectrum conjecture. This is a provenance defect in MathDB's supplementary association, not the mathematical result proposed here.

The 2026 version of record exists: Discrete Mathematics 349, article 114721, DOI 10.1016/j.disc.2025.114721. The DOI response is a linkinghub HTML refresh page, not the article body. Search-visible abstracts and snippets do NOT clear that body. Do not presume the conjecture survived unchanged into it. Current citing-work / correction inventory is incomplete.

## Ordinary proof of the missing inclusion

Fix n≥2 and 1≤k≤n−1. For any k-element D⊆{1,...,n−1}, put E={1,...,n−1}∖D; thus |E|=n−1−k. Every independent set A of G(P_n,D) has at most n−k vertices. Indeed, if A is nonempty, let a=min A. The map x↦x−a sends A∖{a} injectively into E: these differences are positive, at most n−1, and cannot lie in D since A is independent. Therefore |A|−1≤|E|. The empty case is immediate.

Consequently a proper colouring with q colours has n≤q(n−k): partition the vertices into its q independent colour classes and sum the bound. Under the literal hypotheses for m, k>n−ceil(n/m), whence ceil(n/m)>n−k, and therefore n>m(n−k). (For a positive integer m and integer b, ceil(n/m)>b iff n>mb.) A proper colouring with at most m colours is impossible. Thus χ(G(P_n,D))≥m+1 for every D. The natural-order greedy argument gives χ≤k+1. Together with the source's fully stated and proved Theorem 2.3, this proves the entire literal Conjecture 2.1.

There is no missing ordinary lemma in this argument. In particular, the bound is for every D, not an asymptotic statement or a fixed range.

## Independent construction and stronger exact endpoint

The entire spectrum, for all n≥2 and 1≤k<n, is

    Spec(P_n,k) = {q∈N : ceil(n/(n−k)) ≤ q ≤ k+1}.

Here is a construction avoiding any unformalized invocation of Theorem 2.3. Fix such q. From q(n−k)≥n follows ceil(n/q)≤n−k. Among 1,...,n−1 there are n−ceil(n/q) numbers not divisible by q, at least k of them. They contain 1,...,q−1. Choose D of cardinality k containing 1,...,q−1 and contained in those nonmultiples. This is possible since q−1≤k. Colour vertex x by its residue modulo q. An edge has a nonzero difference modulo q, so the colouring is proper. The first q consecutive vertices form a clique because all distances 1,...,q−1 lie in D. Thus χ=q. This handles q=k+1 as well, with D={1,...,k}. The lower bound was proved above. Under the literal m inequalities, ceil(n/(n−k))=m+1; alternatively use the direct m-colour contradiction above.

## Significance objection for root

The new step is the translate-from-the-minimum injection, followed by colour-class counting. It is elementary and closely related to the standard bound χ≥|V|/α. It is not obtained by evaluating the source's printed data or modifying a printed obstruction, and the missing lower inclusion is not proved in the arXiv source. Nevertheless the campaign excludes routine bridges: root should decide whether this short direct argument clears that standard before spending Pi effort. Do not silently promote it because it resolves a labelled conjecture. No global priority is claimed.

## Exact next Pi task, after root qualification

No search is needed. Define the graph on Fin n with adjacency u≠v and Nat.dist u.val v.val∈D. Define the spectrum by existence of a k-element D and the actual finite chromatic number (or a proved equivalent least-colourability definition). Prove:

1. For every independent A, card A≤n−k using min' and the injective image x↦x−min' A into the complement of D. Include positivity, upper bound, exclusion from D, and injectivity bridges.
2. Sum fibre cardinalities of an arbitrary proper q-colouring to obtain n≤q(n−k).
3. Natural-order greedy (at most k earlier neighbours) gives k+1 colourability; alternatively prove a finite greedy lemma directly.
4. For each target q, count nonmultiples in Icc 1 (n−1), choose the prescribed-cardinality extension of Icc 1 (q−1), prove the residue colouring proper, and certify the q-clique.
5. Conclude the all-n,k spectrum identity and restate exactly with the literal m/ceil hypotheses, with no omitted quantifiers.

Expected proof is symbolic and finite-set based, not a large computational certificate. It needs finite simple graphs, independent sets, finite colourings / chromatic number, finite cardinality and elementary division. No real analysis, SAT, external unverified theorem, or numerical evidence is needed. Pin dependencies, audit all theorem axioms, disallow sorry/admit/axiom/unsafe/native_decide, and leave replay/independent fidelity to the assigned Pi and root workflow. This packet itself does not authorize starting that work while the qualification holds remain.
