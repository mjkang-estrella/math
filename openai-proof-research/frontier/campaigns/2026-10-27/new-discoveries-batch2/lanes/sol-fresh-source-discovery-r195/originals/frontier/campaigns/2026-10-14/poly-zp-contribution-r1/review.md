# Independent contribution review, round 1

**Verdict: TECHNICAL, for the whole original package.**

Review completed 2026-10-16 at the requested normal/default speed. Candidate author: Myeongjin Kang, no affiliation. This is an independent contribution assessment, not the separately assigned proof review. No proof PASS is assumed or issued here. The assessment below remains TECHNICAL even if that review validates every assertion. No author file was edited; no acceptance, counting, staging, commit, external message, publication, or submission was performed.

The universal residue is an attractive and potentially useful observation about subgroup arithmetic. The exact theorem was not located verbatim in the bounded primary-source search. That does not make it a substantial contribution. The candidate's sole proposed new mechanism has a direct reconstruction from the GRV torsor/exponential-count description by decomposing an invariant multiset into cyclic orbits of transitive types. Its complementary modulus is then the degree cutoff in that same Euler product. The passage to the length-only residue is induction plus the already explicit abelian lattice formula. I do not find an additional nonroutine obstruction solved by the full package.

This is **not a DUPLICATE verdict**: I have not identified a prior primary theorem stating the whole result with the exact quantifiers. Exact publication novelty remains unsettled. It is also not an UNRESOLVED contribution verdict: the explicit reduction in Section 3 gives positive evidence for TECHNICAL, independently of whether a closer duplicate eventually turns up.

## 1. Frozen object and full original scope

Reviewed in full: `fresh-structural-discovery-r3/candidate.md`, 20,103 bytes, SHA256 `e3f4c65e5eb0f35e9d19090e0ba897b27219a223795a0569319a3114cb3babcc`. The detached seal is SHA256 `75df70d930c3ccd57287e76a082dab1885bb844b0691132201ce2d4a199684e4`. Both match the handoff. I read the full checker, verifier, README, source contracts, provenance, literature record, and both retrieval records. The original verifier independently reran successfully: 79 inputs, 12 outputs, 39 pinned Git blobs, zero writes, no network, receipt SHA256 `fa29613888a882122bfb65afbc7f0410a50c1b93b711361d06e5c8c4f6a68e32`. This is integrity and finite-check evidence only.

The verdict covers all of the following as **one package**, without narrowing:

* Every prime, including 2; every finite iterated extension E of Z_p with a subnormal closed series of length t >= 1; every open U <= E; every h >= 0; actual subgroup counts a_h(U), not subgroup conjugacy counts; congruence to both A_h(t) and c_t modulo p^(h+1).
* Every closed J <= E, its induced length r <= t, the separate trivial-group convention, and the same assertions for every open subgroup of nontrivial J.
* (SC) for every indicated open U, every finite continuous U-set, and all h; the common p-adic limit; recovery of length from that limit; uniform sharpness witnessed only at Heisenberg h = 1 for all primes.
* Lemma 1 for **any finitely generated pro-p kernel N**, with torsion allowed and an arbitrary continuous Z_p action. No nilpotence, solubility, finite rank, uniformity, or large-prime assumption is inserted into this lemma.
* The exact weighted formula sum_{a+b=h} p^b f_b(p^a) on **N-conjugacy classes** of kernel subgroups, with the varying action power p^a.
* All of Theorem B, including finitely generated pro-p Gamma, infinite abelianization, the bound l on generator numbers of every finite quotient of every closed subgroup, and all three equivalent conditions with t in [1,l]. Its source-dependent extraction remains part of the reviewed scope, although it is credited prior mathematics.

No separate credit is assigned to the action lemma, residue, characterization, SC, closed-subgroup statement, limit, length recovery, or example. Nothing here evaluates a substitute restricted to nilpotent groups, uniform groups, odd primes, normal subgroups, or a fixed subgroup index.

## 2. Exact pinned-source comparison

The stipulated input is OpenAI's *Cyclic length and chromatic fixed-point loss* at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Its truth is accepted as instructed. I read all of `01-introduction.tex`, `04-congruences.tex`, and `05-profinite.tex`, including the proofs at the used interfaces, and the entire bibliography. Hashes, byte lengths, URLs, and detailed read boundaries are in `read-extents.json` and the input manifest. The other sections were term-searched for overlapping subgroup/residue statements; they were not all proof-read. The complete preprint tree was parsed for companion paths (13,223 entries, `truncated: false`); only this family contains `05-profinite.tex`. This is a companion screen, not an argument for novelty.

The main source theorem `thm:procyclic` assumes a finitely generated pro-p group, l >= 0, the finite-section generator bound, p-integrality of continuous homomorphism counts for **every finite target**, and SC for **every open subgroup and every finite continuous set**, and extracts the Z_p-factor series. The candidate's Theorem B replaces the initial use of homomorphism integrality by its explicit infinite-abelianization hypothesis. The source already explains that the integrality condition supplies just this first quotient in this argument. That substitution is routine, as the candidate acknowledges.

`lem:shrinking-action` assumes K is pro-p, d,l >= 0, that K x Z_p^d has SC on all its open subgroups, and the finite-section bound for that product; an epimorphism K -> Z_p has kernel N. It concludes SC and the same section bound for N x Z_p^(d+1). Its proof uses slowed actions on open subgroups and a common finite permutation quotient. It is a qualitative **forward** transfer to the trivial action; it does not itself state finite-precision action comparison or reverse preservation of SC.

`lem:kernel-abelianization` assumes nontrivial finitely generated pro-p K, d >= 1, and SC for K x Z_p^d (with the source's all-open convention). It concludes infinite abelianization of K, through the Frattini full-mark detector, graph-subgroup count, and a nonzero abelian lattice limit. The candidate's repeated extraction and the rank-d+1 termination test are the source's argument, not a new classification method.

`lem:lattice-limit` already gives the abelian generating product, coefficients divisible by the appropriate p powers, and c_d as its nonzero p-adic limit. The finite truncation error modulo p^(h+1) is immediately visible in its proof. `04-congruences.tex` already gives the actual-subgroup normalization through pointed transitive sets and logarithmic extraction, citing Tamanoi. These are strong operation-level premises; the candidate does not earn credit simply by placing an equivalence around them.

The real increment over the pinned source is the reverse SC conclusion for all poly-Z_p groups, obtained through the finite-index action comparison. That increment is real relative to this source's statements. Section 3 assesses its mathematical cost against the older counting mechanisms.

## 3. Explicit standard-operation reduction of the proposed new mechanism

Here is my reconstruction. It explains why the objection about a short standard combination is substantive rather than a reaction to proof length. This deduction is the reviewer's inference from the cited primary operations, not a claim that GRV prints the candidate's formula.

Fix h. For a finitely generated pro-p N there is an open characteristic O contained in every subgroup of index at most p^h: intersect the kernels of continuous maps N -> Sym(p^h), padding smaller actions with fixed points. The intersection is finite because N is finitely generated. Continuity of the given action makes its action on P = N/O have p-power order. Every index-p^h subgroup of N semidirect Z_p contains O: its intersection with N has index p^b for some b <= h. Thus the subgroup count in question is preserved by replacing N by the finite p-group P. The same holds for the direct product. Conjugacy classes and their action at the relevant indices are preserved as well. This requires neither torsion-freeness nor analytic structure.

For the moment use the discrete group D = P semidirect_alpha Z. It is finitely generated, so GRV Proposition 3.1 and Corollary 3.2 apply to every finite symmetric target. The restriction fiber is a centralizer torsor. Their Section 5 identifies

    F_alpha(x) = sum_n |Hom(D,Sym(n))| x^n/n!

with the ordinary generating function of alpha-fixed isomorphism classes of finite P-sets, and also with

    exp(sum_{n>=1} u_n(D) x^n/n),

where u_n(D) counts actual index-n subgroups. The fixed class is an underlying P-action fixed up to isomorphism; no choice of an intertwiner is counted in this ordinary generating function.

A transitive P-set has size p^b and is determined up to isomorphism by a P-conjugacy class of index-p^b subgroups. Let o_(b,j) be the number of alpha-orbits of length p^j on these transitive types. A finite P-set is an unordered multiset of transitive types. Its class is alpha-fixed exactly when multiplicities are constant around every orbit. One such orbit therefore contributes the elementary geometric factor

    (1 - x^(p^(b+j)))^(-1).

Consequently the **same GRV counting description** gives

    F_alpha(x) = product_(b,j) (1 - x^(p^(b+j)))^(-o_(b,j)),
    F_1(x)     = product_(b,j) (1 - x^(p^b))^(-p^j o_(b,j)).

Only finitely many relevant factors occur in each degree. The first formula is orbit decomposition of an invariant multiset, not an additional subgroup-growth theorem. In particular an indecomposable invariant multiset can contain several transitive P-orbits cycled by alpha; confusing it with a single alpha-fixed transitive P-orbit loses exactly the j parameter under review.

Take p^h times the coefficient of x^(p^h) in the logarithm. One factor of degree p^(b+j) contributes p^(b+j) if b+j <= h and zero otherwise. Hence

    u_(p^h)(D) = sum_(b+j<=h) p^(b+j) o_(b,j)
               = sum_(a+b=h) p^b f_b(p^a).

For the trivial action, its contribution is p^(b+j) whenever b <= h. Subtracting gives the exact expression

    u_(p^h)(D) - u_(p^h)(P x Z)
      = - sum_(b<=h, b+j>h) p^(b+j) o_(b,j).                 (*)

Every summand is divisible by p^(h+1). There is no cancellation to control, estimate to improve, new cohomological vanishing, or extra structure theorem to supply. The complementary indices a+b=h in the candidate are simply the logarithmic degree cutoff b+j<=h in this product. Equivalently, the elementary cyclic-p orbit argument says that k_b-f_b(p^a) is divisible by p^(a+1); multiplying by p^b gives the same statement.

For completeness, the discrete-to-pro-p interface in this reduction is elementary but must be stated correctly. It is **not** true that every arbitrary permutation representation of D of p-power degree is a pro-p representation. We need only its transitive index-p^h subgroups. Such an H projects to p^a Z and contains a lift gT^(p^a). If alpha has order dividing p^e and the finite p-group P has exponent dividing p^s, then

    (gT^(p^a))^(p^e) = u T^(p^(a+e)),
    (gT^(p^a))^(p^(e+s)) = T^(p^(a+e+s))

for some u in P; the second equality follows because the displayed T-power centralizes P. Thus H contains a central normal subgroup generated by a sufficiently large p-power of T. It is the preimage of a subgroup of the finite p-group P semidirect C_(p^L). Conversely every open subgroup of P semidirect Z_p restricts to one in D, and these finite p-quotients give a bijection. Therefore u_(p^h)(D) is precisely the continuous open-subgroup count a_h(P semidirect Z_p); likewise for the direct product. Together with the characteristic-quotient reduction, (*) recovers **all** of Lemma 1, including arbitrary finitely generated kernels, torsion, every continuous action, and p=2.

The candidate's direct transporter proof is a clean alternate presentation of this same count. For a fixed V it counts [N_N(V):V] admissible lift cosets; there are [N:N_N(V)] representatives of its conjugacy class. Their product is [N:V]=p^b. This is the subgroup version of torsor-fiber times orbit-size cancellation in GRV Lemma 2.1. Tamanoi's proof of Theorem 5-5 explicitly converts the reciprocal automorphism/normalizer factor into an actual-subgroup count with the identity

    [N:N_N(V)] [N_N(V):V] = [N:V].

The symbols occur in a different application there, but the normalization operation is already explicit. No hidden theorem identifies actual subgroups with unweighted conjugacy classes. The proposed formula gets this point right; getting a standard weight right is necessary, but it does not by itself provide a new structural contribution.

Kisilevsky Proposition 1 is formally stated for a discrete Z_p-module A with finite fixed layers A_n. Its proof uses only the underlying finite cyclic-p set: newly appearing elements lie in orbits of size p^(n+1). To apply the operation to subgroup classes one uses that proof on the underlying finite set, rather than pretending the set of classes is already a module. Telescoping fixed-layer differences up to the eventual full finite set gives k_b-f_b(p^a) divisible by p^(a+1). This is exactly the orbit step in the candidate.

This is an explicit full-scope reduction to established counting operations. It does not depend on finding the final displayed congruence verbatim in an index or on assuming that wide quantifiers are cheap. Rather, the finite characteristic quotient and orbit product explain why those quantifiers introduce no further difficulty here.

## 4. What remains after the action comparison

The passage from an arbitrary length-t poly-Z_p series to Z_p^t makes t applications of Lemma 1 to K_i x Z_p^i. Quotient Z_p splits by the elementary procyclic lifting fact. Applying the lemma to the entire product kernel, rather than trying to propagate a congruence in bare a_h(N) through conjugacy counts, is the right bookkeeping. It preserves the modulus automatically at each step; it supplies no new counting obstruction beyond Section 3.

Tamanoi 2001 Lemma 5-5 already gives the exact Hermite-basis lattice count. The pinned lattice-limit proof already writes A_h(t) as the partial sum of b_j with p^j dividing b_j. The tail from j=h+1 is therefore in p^(h+1) Z_p, yielding the displayed c_t residue. Thus the explicit residue is a useful endpoint of the induction, not a second nonroutine mechanism.

Intersections with a finite subnormal Z_p series give the open/closed subgroup assertions using that a closed subgroup of Z_p is zero or Z_p. Finite generation, the t-generator bound, and length preservation for open subgroups follow at the same time. These require no Lie classification or prime-dependent input; their wide scope is respected in the reduction.

For a transitive U-set U/W, the SC sum is exactly p^m[a_(h-m)(W)-a_h(U)] when h>=m=log_p[U:W], and the small-index case is immediate from |U/W|. Disjoint union handles every finite U-set. This is ordinary pair counting/marks, adding no separate invariant beyond the universal residue. Theorem B's other direction is precisely the stipulated shrinking/kernel extraction already discussed.

The difference c_(t+1)-c_t has valuation t; the resulting length recovery is elementary p-adic first-nonzero-term arithmetic. The Heisenberg computation a_1=p+1 versus A_1(3)=1+p+p^2 follows from its two-generator Frattini quotient and correctly proves only the stated uniform sharpness at h=1. Neither is an extra contribution. A proof gate should still examine all these deductions independently; this section makes a contribution comparison, not a substitute proof certificate.

## 5. Primary literature and the fresh dissertation lead

**GRV.** Gordon and Rodriguez-Villegas, *On the divisibility of #Hom(Gamma,G) by |G|*, J. Algebra 350 (2012), 300-307. [Primary versioned PDF](https://arxiv.org/pdf/1105.6066v1). Full seven-page body and references read. Lemma 2.1 provides torsor/orbit cancellation; Proposition 3.1 and Corollary 3.2 provide the semidirect-product fixed-class count for a discrete kernel and finite target (with the semidirect product finitely generated for finiteness); Section 5 gives the symmetric-action exponential relation, product exponents, direct-product conjugacy interpretation, and Proposition 5.1's adjacent-index congruence. Proposition 5.1 by itself does **not** compare two actions or identify c_t. Section 3 above uses the stronger operations preceding that proposition, not just its stated congruence. The retained PDF has an arXiv-v1 margin and an internal 2021 date; no publication chronology is inferred from that discrepancy.

**Solomon.** Louis Solomon, *The solution of equations in groups*, Arch. Math. 20 (1969), 241-247. [Primary publisher PDF](https://link.springer.com/content/pdf/10.1007/BF01899292.pdf). Freshly retrieved; full paper read, including its equivalence-class cardinality argument (especially Lemma 4) and generator-change reduction. Its theorem requires m<n words in a free group on n generators, a finite target G, and prescribed conjugacy classes; the solution count is divisible by |G|. It does not print the present subgroup congruence. It is a historical divisibility antecedent; no unrestricted application to arbitrary finitely generated kernels is inferred from its presentation hypothesis. GRV supplies the more convenient exact operation used above.

**Kisilevsky.** H. Kisilevsky, *A generalization of a result of Sinnott*, Pacific J. Math. 181(3) (1997), 225-229. [Primary publisher PDF](https://msp.org/pjm/1997/181-3/pjm-v181-n3-p11-p.pdf). Full paper read, applying only Proposition 1 and its proof on p.225 as comparison. Exact module hypothesis and the underlying-set extension are distinguished in Section 3. The complementary orbit divisor is this elementary operation.

**Tamanoi.** *Generalized orbifold Euler characteristic of symmetric products and equivariant Morava K-theory*, AGT 1 (2001), 115-141, [primary PDF](https://msp.org/agt/2001/1-1/agt-v1-n1-p06-p.pdf), pp.139-140, Corollary 5-4, (5-8), full Lemma 5-5 proof, through (5-10), read. Also *Generalized orbifold Euler characteristics of symmetric orbifolds and covering spaces*, AGT 3 (2003), 791-856, [primary PDF](https://msp.org/agt/2003/3-2/agt-v3-n2-p06-p.pdf), pp.825-828 including Proposition 5-4, full Theorem 5-5 proof and (5-5)-(5-7), Lemma 5-6, read. The 2003 invariant statement concerns finite G and a G-manifold M; its M=point/G=trivial specialization gives the ordinary subgroup exponential formula. Normalizer/automorphism weights are explicit in the proof. I do not invoke its whole bundle theory as a premise for a new theorem.

**Frankel: the parent-provided fresh lead was read, and is relevant.** Brett Frankel, *Representations of Fundamental Groups of Abelian Varieties in Characteristic p*, University of Pennsylvania PhD dissertation, 2016. [Primary institutional PDF](https://repository.upenn.edu/bitstreams/06a689f2-8398-4072-8b8b-1e398d8986ce/download). Title/metadata and **all of Chapter 4, printed pp.23-29**, with every proof, read; the bibliography was checked for the cited Solomon/GRV references. Rendered Theorem 13 and Proposition 17/proof pages were inspected to resolve extraction typography.

Theorem 13 treats a topologically finitely generated profinite kernel, arbitrary continuous semidirect action of the procyclic completion away from a set S of primes, and finite target G; it gives the homomorphism ratio in S^(-1) Z and the converse characterization. Proposition 17 specifically gives p-integrality of |Hom(Gamma semidirect Z_p,G)|/|G|. The proof must restrict the image of the topological generator to p-power order. It combines centralizer-coset counting with Lemma 16, proved using Frobenius divisibility. For S consisting of every prime other than p, its cyclic factor is Z_p and its localization is Z_(p).

This is an existing profinite GRV analogue, so a claim that merely passing torsor divisibility from Z to Z_p supplies the novelty would be untenable. It is broader than the candidate in allowing non-pro-p profinite kernels, but **does not** give a_h(action)=a_h(trivial) mod p^(h+1), SC, or the poly-Z_p residue in the chapter read. General finite-target centralizers can have other prime factors, which is why its proof needs a p-element coset-divisibility step. I do not identify its integrality theorem with the stronger exact fixed-class equality used for discrete GRV. The candidate's finite-p-kernel reduction is the elementary way to bypass that distinction for this subgroup question. There is also a visible wording slip in Theorem 13's explanatory line naming G as a semidirect factor; the notation and Section 4.2 unambiguously use the indicated procyclic factor. This does not affect its relevance.

**Specialist subgroup congruences: inspected rather than presumed absent.** T. W. Mueller and J.-C. Schlage-Puchta, *Divisibility properties of subgroup numbers for the modular group*, NYJM 11 (2005), 205-224, [primary journal PDF](https://nyjm.albany.edu/j/2005/11-11p.pdf). Fresh retrieval; full pp.205-207 statements and the start of the recurrence proof on p.208 read. Its groups are PSL_2(Z) and specified virtually free relatives, with higher 2-power congruences for actual subgroup numbers and free subgroup numbers and a mod-3 description. Those are genuine arithmetic results but not a theorem about all soluble pro-p kernels or action independence. Its later digital-recursion proofs were not read in full.

C. Krattenthaler and T. W. Mueller, *Truncated versions of Dwork's lemma for exponentials of power series and p-divisibility of arithmetic functions*, [primary arXiv PDF, retrieved v2](https://arxiv.org/pdf/1412.7014), 34 pages. Fresh retrieval; introduction and Lemma 1, Theorem 2 statement, Theorems 17-19 with their short proofs, Theorem 25/proof and Theorem 26, and Theorem 27 with its proof opening read (exact text line boundaries in the read log). Theorem 2 assumes explicit truncated Dwork and coefficient-valuation conditions; it does not provide action comparison without checking those conditions. Theorems 25-26 concern homomorphism valuations for **finite abelian p-groups**; the proof records refined adjacent subgroup-number divisibility (6.8)-(6.11). Theorem 27 treats listed **free products** and eventual periodicity modulo a fixed p. Neither the finite-abelian hypothesis nor free-product hypotheses can be silently promoted to the candidate's poly-Z_p class. Their standard exponential/counting infrastructure strengthens the technical-combination concern, but I have not used these theorems to declare the candidate a duplicate.

## 6. Bounded search, evidence, and limitations

Fifteen fresh search queries were made, grouped around pro-p subgroup-count congruences, polycyclic/polyprocyclic counts, p-adic subgroup numbers, semidirect-product comparison, specialist Mueller results, Kulakoff-type congruences, Solomon, and the dissertation title. `search-log.md` records their exact strings, discovered primary URLs, and failures. Four fresh primary PDFs were downloaded: Frankel, Solomon, Mueller--Schlage-Puchta, and Krattenthaler--Mueller. The inherited GRV/Kisilevsky/Tamanoi reading copies were read at the extents above and their exact bytes authenticated. The author screen's wrong-title Frenkel retrieval is preserved as such, not used as evidence.

Web results were discovery aids. Only primary texts support the mathematical comparisons. Search noise included congruence-subgroup growth (a different meaning of congruence), semigroup congruences, and non-primary mirrors; these were not mathematical premises. The web open of the institutional dissertation failed, but direct HTTPS retrieval succeeded and the title, chapter and proofs were inspected locally. No paywalled database-wide MathSciNet/Zentralblatt search, every-language search, citation-network exhaustion, or worldwide-priority audit was performed. Not every specialist subgroup-growth text was read; exact duplication in that literature remains possible.

`comparison_checks.py` was written independently, without importing the candidate's code. It enumerates all subgroups of D8 semidirect C4 under r->r,s->rs and of D8 x C4; independently forms the kernel conjugacy-class action and GRV orbit Euler factors; extracts actual subgroup counts by xF'/F; and compares them with the candidate's weighted expression and (*). At h=0,1,2, the actual counts are (1,3,11), the direct counts (1,7,19), and differences (0,-4,-8). There are 34 versus 62 total finite subgroups; the factor-degree lists are recorded in `comparison-receipt.json`. Another 384 exact single-orbit tests check the degree cutoff for p=2,3,5. These computations confirm the normalization and cutoff in this example; they do not establish the universal theorem, priority, or importance.

No counterexample to the candidate's mathematics is asserted. No proof-review conclusion from another agent was read or assumed. The contribution assessment is an independent comparison that also reconstructs the proposed core by established operations.

## 7. Required repairs and optional improvements

**Required for an honest contribution disposition:**

1. Retain this as a **technical theorem/corollary package**, rather than a completed substantial campaign result, unless a further nonroutine contribution is proved and independently reviewed. No wording edit, new name for the characterization, enlarged list of consequences, or broader recitation of its quantifiers repairs the present substantiality failure. This is the decisive contribution issue.
2. Any subsequent manuscript asserting novelty of the finite-precision action comparison must explicitly address the orbit Euler-product reduction in Section 3, including its finite characteristic-quotient and discrete/pro-p interfaces. Merely noting that GRV Proposition 5.1 compares adjacent indices does not address the stronger mechanism in GRV's preceding exact counting description.
3. Add the relevant Frankel Chapter 4 antecedent to the literature account if the package is retained. Distinguish his p-integrality theorem from an exact fixed-class identity, and continue crediting the source's extraction, Tamanoi's lattice formula/normalization, and Kisilevsky's underlying orbit argument. An exact-new-to-source residue alone must not be presented as evidence of a nonroutine advance.
4. Keep proof and contribution gates separate, preserve every original quantifier, and preserve the original frozen candidate and source rights. This review authorizes no acceptance or campaign increment. Mathematical proof repairs, if any, belong to the separately assigned proof review; none is certified unnecessary here.

**Optional:** present the exact omitted-orbit expression (*) alongside the transporter proof, because it makes the source comparison transparent; state the nonpositive sign of the action/direct difference as an explanatory feature, without counting it separately; streamline the redundant credited consequences around the one core count; and broaden specialist literature screening if preparing a technical note for publication. These improvements would improve exposition or priority confidence, not change this verdict by themselves.

## 8. Provenance, read boundaries, and reproduction

All review writes are under `frontier/campaigns/2026-10-14/poly-zp-contribution-r1/`. The complete candidate snapshot, with its original manifests and seal unchanged, is under `inputs/private/frozen-candidate/`. Context snapshots and third-party literature/rendered pages are private/local inputs and retain their original rights. The input inventory gives SHA256 and byte lengths for each such file. `read-extents.json` distinguishes reading, searching, authentication, and mere retention; no claim is made to have read every inventoried input. `commands.md` records the actual consequential commands and replay instructions.

Original review prose is CC BY 4.0; original review code is MIT. Author metadata retained: Myeongjin Kang, no affiliation. These licenses do not relicense OpenAI source copies, primary papers, dissertation, rendered pages, or other third-party material. Nothing has been uploaded or submitted. `RIGHTS.md` and the original candidate rights notice preserve that boundary.

Run `python3 -B verify.py` in this directory after authenticating its detached seal hash from the handoff. It authenticates immutable input/output inventories and stored receipts **before** replay, reruns the frozen original verifier on the private snapshot, and compares the independent check output byte-for-byte. It writes nothing and does not reseal or regenerate receipts. A successful replay verifies the evidence package, not substantiality or the separately reviewed mathematical proof.
