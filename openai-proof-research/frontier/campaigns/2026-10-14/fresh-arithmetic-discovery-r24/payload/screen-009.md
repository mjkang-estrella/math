# Family 009: Hom reconstruction screen (no nomination)

Myeongjin Kang, no affiliation; original prose CC BY 4.0. This is an author-side operation comparison, not a frozen theorem or an independent review. Pinned source truths are stipulated. The full Isom theorems are not audited.

## Chronology and scope

Family 009 was announced to the parent and both other discovery agents before mathematical development. The three source introductions were read, then all five sections of the equal-characteristic companion. No full Hom theorem was frozen: the exact class of geometric noninjective maps was still under selection. The following failures therefore are pre-freeze screening, not a weakened replacement theorem. The current accepted count is 13; this screen changes it by zero.

A tempting target was to reconstruct embeddings from compatible injective maps of degree-one and degree-two Milnor groups modulo p, for every finitely generated extension of algebraically closed fields of characteristic p and relative transcendence degree at least two. The source's actual operations show why that is not a credible substantial nominee by itself.

## What the existing proof already supplies

Write H=K^p, C=L^p. Let theta:K*/K*^p -> L*/L*^p be injective and preserve Steinberg relations. Suppose its image contains representatives X,Y which are p-independent over C. In source `04-lines.tex`, the complete multipartite graph on nonzero source classes is partitioned by degree-p target subfields C(X). The only use of surjectivity in constructing this graph is to guarantee at least two parts. The stated image hypothesis gives those parts directly. Every vertex has a neighbor and graph diameter is at most two.

The source's affine configuration u=x+a, v=y+b, z=bx-ay=bu-av, for a,b in H*, then survives unchanged. Source `02-symbols.tex` `lem:zero-symbol` places image classes in C(X), C(Y) and two multiplicative translates. Injectivity supplies the nonmonomial conditions. Source `03-intersection.tex` `prop:intersection` yields the unique common exponent, and the graph propagates it. Thus one scalar multiple of theta maps all H-projective lines into C-projective lines. This is precisely the source proof before its final inverse-map argument, not a new operation.

Finishing an embedding theorem requires the appropriate non-surjective fundamental theorem of projective geometry, with exact nondegeneracy hypotheses. I have not silently substituted the source's bijective `prop:projective-lift`: it explicitly uses an inverse, preservation of spans, and matching bases. Even if that classical extension is paid, no new source-specific mechanism has been found. This injective transfer is not nominated. The closest older operation is Bogomolov–Tschinkel, *Milnor K2 and field homomorphisms*, Theorems 2 and 4 (actual author PDF introduction read): injective multiplicative maps preserving one-variable subfields are lifted to field embeddings, after a common power correction. Their quotient is by constants/infinitely divisible elements in characteristic zero, not the present mod-p quotient. The source itself already credits the differential power correction and projective lifting to predecessors.

## Genuine noninjective maps are not an exceptional corner

For every prime p let k be algebraically closed of characteristic p, L=k(x,y), K=L(t), and fix any h in L*. For f in K*, write

    f = t^m (a + higher powers of t),  m in Z, a in L*.

Define psi_h([f])=[a h^m] in L*/L*^p. The leading coefficient is taken in the t-adic expansion, so multiplication makes psi_h a group homomorphism. A pth power has valuation pm and leading coefficient a^p, hence maps to a pth power. It therefore descends to an F_p-linear map on V_K.

It preserves every Steinberg relation. If v_t(f)>0, the leading term of 1-f is 1 and its image is trivial. If v_t(f)<0, f and 1-f have the same valuation and opposite leading coefficients; their images are a h^m and -a h^m, whose symbol is {b,-b}=0. If v_t(f)=0 and its residue a is not 1, the images are a and 1-a. If a=1 then the image of f is trivial. These cases exhaust f not equal to 0 or 1. Thus the tensor map factors through K2^M(K)/p -> K2^M(L)/p.

The image contains [x] and [y], which are p-independent, and is surjective on V_L. The kernel contains [1+t], a nonzero class: its derivative with respect to t is 1, whereas pth powers have zero derivative. Consequently nondegenerate compatible maps need not be injective, even when their image has full target p-rank. For h not a pth power, psi_h([t])=[h] is nonzero. Therefore a formulation which merely says “take the residue of every element” does not describe the homomorphism: valuation-group choices must also be included. On units the map is residue; on uniformizer powers it includes an independent value-group contribution. This is an elementary necessary example, not a classification theorem or a novelty claim.

There is a separate inseparable field-embedding phenomenon. On K=k(x,y,z), the field embedding x->x, y->y, z->z^p induces a Steinberg-compatible map with nonzero kernel on V_K (it kills [z]) and still has p-independent images [x],[y]. Its noninjectivity is not evidence that the original field map is a place. A full Hom statement must allow this mechanism as well as valuation specializations.

## Why the closest primary classification does not close the gap

Bogomolov–Rovinsky–Tschinkel, *Homomorphisms of multiplicative groups of fields preserving algebraic dependence*, Theorem 2, has target L*/ltilde*, with ltilde relatively algebraically closed in L. Its dependence relation is transcendence-degree-one dependence over ltilde. The proof of Lemma 17 explicitly uses relative algebraic closedness. In the mod-p setting C=L^p is not relatively algebraically closed in L: every element of L is algebraic over C. Transcendence dependence over C is therefore identically trivial. The useful relation here is equality of degree-p subfields C(X), not the primary theorem's relation. Substituting C for ltilde invalidates both hypotheses and proof.

There is an additional concrete obstruction in the primary's final valuation descent (Lemma 33). It explicitly uses torsion-freeness of L*/L_2* to deduce strict rational-rank loss for the kernel in the value group. Our target V_L has exponent p. For the elementary value map Z -> F_p, reduction modulo p, the kernel pZ has the same rational rank as Z and its nonnegative elements are not a convex subgroup. Thus that descent operation cannot simply be copied. This does not refute a different mod-p classification.

For a noninjective theta, the source affine configuration can lose its nonmonomial image: [x+1] can coincide with a scalar multiple of [x], even when a p-independent image pair exists elsewhere. The specific unpaid bridge is a plane-by-plane classification of these collapsed configurations, followed by a global compatible valuation/subfield structure that handles exponent-p value groups and inseparable embeddings. Neither a global source inverse nor the primary's torsion-free descent is available. No such plane classification or gluing mechanism has been proved here.

## History and reading limits

The r39 history index points only to the actual structural-r15 catalogue screen for family 009; that full screen was read and contains no developed reconstruction target. A bounded search of all saved authored artifacts by Bogomolov, Milnor theory/groups, anabelian, Steinberg relations and function-field reconstruction found only unrelated Campana/Bogomolov-sheaf passages. An initial broad command also searched inherited task JSON and produced a very large truncated output; that output is not treated as complete reading or clearance. Current-history checking remains bounded.

Read directly: all three pinned introductions; all equal-characteristic sections 01–05 and references bibliography; BRT author PDF extraction lines 1–270, 650–755, 1103–1185, 1260–1320; BT author PDF extraction lines 1–240. The other two companions' remaining proofs are authenticated but not read, and no claim is based on their uninspected operations. Cadoret–Pirutka arXiv v3 fetch returned 404; no body-reading claim for that failed fetch. Third-party PDFs/extractions and pinned source bodies are kept under ignored private/ and are excluded from Git/releases.

Disposition: NO NOMINEE. Injective Hom transfer is source-paid plus a classical lifting obligation; unrestricted nondegenerate Hom reconstruction has the precise new collapsed-plane and exponent-p valuation-descent gap above. No restricted result is substituted for a full theorem.
