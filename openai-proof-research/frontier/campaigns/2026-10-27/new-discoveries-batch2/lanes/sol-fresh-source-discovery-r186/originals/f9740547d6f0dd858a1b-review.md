# AGM063 independent contribution and eligibility review, round 1

**Verdict: SUBSTANTIAL (moderate strength), for the complete unchanged AGM063 target in fixed-scope.md, conditional on the separate proof gate passing proof.md §§2–6 without adding hypotheses or narrowing scope.** Not DUPLICATE, not INELIGIBLE, not BLOCKED.

This is a contribution verdict only. It is not a proof verdict, an acceptance, a count change, a Lean/formal claim, a manuscript gate or a publication. The reviewer is not an author of AGM063 and did not read the separate proof-gate output (none existed at reading time) or derive a replacement proof. Per the brief, correctness is assumed only to assess contribution. Mathematical observations made along the way are listed separately in §6. They are not a proof review.

## 1. Target checked

The target is fixed-scope.md (SHA256 03a4861c…7081), read completely. It covers every positive-dimensional smooth connected complex projective Fano n-fold with actual Picard number r and pseudoindex i such that r(i−1)≥n−1, and gives exactly five types with these actual-invariant restrictions:

- Q^i needs i≥3.
- Types 3–5 need r≥2.
- The bundle types need i≥2.
- Q^2 is excluded at actual r.
- Zero exponents mean a point.

There is no dimension, rank, contraction or covering restriction. The equality case is credited to pinned family063 thm:main. The proposed new conclusion is the whole defect-one range.

The end of proof.md compares this with Fujita's parametrised Conjecture AGM^n_ρ (Conj. 1.4, where ρ_X≥ρ). Given S1, the two formulations are equivalent: a strict excess ρ_X>ρ forces i=2 and X=(P^1)^n. I checked that comparison myself against Fujita's statement. Within its own formulation the target is therefore the full pseudoindex form of Fujita's named advanced conjecture, not a narrower substitute. No later narrowing was seen or used to rescue anything.

## 2. What the existing operations already pay

**Pinned source (family063, stipulated).**
- Two results are actually read and stipulated: introduction thm:main (S1, the bound plus equality) and trace.tex prop:independent-correspondences (S2). S2 gives r linearly independent stable-map degrees with S_{γ1}…S_{γr}≠0 and Σ(d_j−1)≤n.
- equality.tex lem:minimum-degree-incidence uses the support of the composed correspondence **only for nonemptiness**: if the incidence fiber product were empty the product would vanish. It extracts one chain, then shows that degree-ι families are proper.
- prop:equality-rigidity then applies the BCDD ordered-chain bound to that single chain, uses cyclic rotation to make every family covering at equality, and finishes with Occhetta.
- Run in defect one, this operation gives only Locus dimension ≥n−1 for each rotated family, so a family may cover only a divisor. That falls short of the r−1 dominating unsplit families that Fujita's Theorem 6.1 needs. The author's contribution-map says the same, and I verified it independently from the source text.
- No pinned-catalogue companion asserts the advanced classification (see reading-limits.md).

**Fujita, Eur. J. Math. 2 (2016) 120–139 (primary, read).**
- Conj. 1.4 states AGM^n_ρ.
- Prop. 1.8 and Rem. 1.9 prove it for ρ≤3 or n≤5, using the rank-one input.
- Thm. 3.2 restates Kollár IV.4.16: fibers are entire rc-equivalence classes over Z^0.
- Constr. 3.5 is the Novelli–Occhetta construction: a minimal dominating family, then minimal horizontal dominating families.
- Lemma 3.6 gives Σ(−K·V^i−1)≤n for those families **without** needing them unsplit.
- Lemma 3.7 bounds k when some family splits.
- Prop. 3.3 gives k=ρ_X when all families are (quasi-)unsplit.
- Thm. 6.1 and Cor. 6.4: if every Constr. 3.5 family is unsplit, there is an extremal ray all of whose fibers have dimension ≤ι−1.
- Thm. 5.2, Lemma 4.2, Prop. 4.3, Cors. 4.6–4.7 and Prop. 5.3(b) are the Picard-number induction and the bundle classification.
- Props. 7.1–7.3 are the only places where Fujita proves the unsplit premise. Each opens with "by Corollary 6.4 it is enough to show that all V^i are unsplit" and then uses range-specific numerical contradictions (Lemma 3.6/3.7 and Theorem 3.4 with ι≥(n+1)/2, ι≥(n+2)/3, or n=5, ι=2, ρ=4).

**Dedieu–Höring Thm. 1.3 (primary, statement read).** This pays the rank-one case ι≥n ⇒ P^n or Q^n and records the gap in Miyaoka's earlier proof.

## 3. Is the full theorem a straight template application? No.

The decisive question is whether S1, taken as a black box, plus Fujita's existing numerical toolkit already yields the unsplit premise of Cor. 6.4. I checked this directly.

Suppose some Construction 3.5 family V^j is split, so d_j≥2i. Lemma 3.6 then gives:

    (2i−1) + (k−1)(i−1) ≤ n ≤ r(i−1)+1,   hence   k ≤ r−1.

This is no contradiction. For split families, Prop. 3.3 provides no lower bound k≥ρ_X, because degenerate components contribute classes. Lemma 3.7, k(i−1)≤n−i, is likewise consistent. Theorem 3.4 needs rc(V)-connectedness by one family and a range condition the defect-one case does not supply.

So the Mukai bound does not close Fujita's template, even when added to it. What is missing is a link between the source's r independent classes and the families that Fujita's construction actually picks. Fujita's organization paragraph calls the special-extremal-ray assumption strong and a possible reason the general case is open. §6 reduces it to unsplit dominating families, and §7 supplies those only in special ranges. It is not finite-union bookkeeping or a robust transfer of a paid estimate.

## 4. The new operations, compared operation by operation

1. **Support dimension, not support nonemptiness (proof §4).** The composed virtual correspondence is a Chow class of pure dimension n+s on X×X. Its support lies in the closed endpoint locus Z of ordered chains. A nonzero class therefore forces dim Z≥n+s≥2n−1 in defect one. The source used the same refined-intersection support fact only to get one chain, and computed the grading only cohomologically. Taking the dimension of the support over pairs of endpoints is a different operation, and the source never performs it. It is short and uses standard Fulton-style intersection theory. Its importance lies in what it controls: a two-endpoint quantity, rather than BCDD's one-point Locus_x bound.
2. **Two-endpoint saturation lemma (proof §3).** Fujita's Thm. 3.2 (full classes) gives Z⊂(X^0×_B X^0)∪(E×E). This excludes a base of dimension ≥2. A compact fiber divisor that avoids finitely many representatives of a spanning set of classes excludes b=1. Together they give rc(V)-connectedness. None of Fujita, the source, or the primary lemmas I read (BCDD-type Lemmas 2.7–2.9, Prop. 2.5/2.6, Thm. 3.4) carries out this upgrade from a codimension-one subset of the chain relation to full chain connectedness. Each ingredient is standard. The combination is the new geometric step, and it is what makes the quantum output usable.
3. **Uniform horizontal-degree control (proof §5).** A finite unsplit rc-connecting collection of degree ≤M bounds by M the degree of the minimal dominating family and of every minimal horizontal dominating family in Constr. 3.5. With M=i+1<2i, every chosen family is unsplit. This is a standard style of argument. My judgement is that this step **alone would be TECHNICAL**. It counts toward the verdict only as the necessary third link.
4. **Final induction (proof §6).** Cor. 6.4, Thm. 5.2, Lemma 4.2, Prop. 5.3(b) and Cors. 4.6–4.7 are a straight existing-template application, and the author correctly credits them. The same goes for the degree<2i unsplit argument (§2; a mild extension of lem:minimum-degree-incidence), the rank-one case (Dedieu–Höring) and the invariant checks (§7). All of these are TECHNICAL.

**Assessment.** The contribution is the chain 1→2→3. It converts a stipulated quantum-cohomological nonvanishing into rational-chain connectedness by bounded-degree unsplit families, and from there into Fujita's unsplit premise, uniformly in n and r. The chain is concise, roughly two pages, and built from standard tools. That is why I rate it moderate rather than strong. It is still a concrete nonroutine operation that neither the source nor the closest primary contains. Fujita's introduction calls the special-extremal-ray assumption strong and a likely reason the general case was open; his §6 reduces that assumption to unsplit families, and §7 proves unsplitness only in special ranges. The chain removes that obstruction, and I showed above that the obvious template route through S1 fails. Solving the named conjecture is not the basis of the verdict. The basis is the operation comparison in §§3–4.

## 5. Eligibility and history (bounded)

- **Source use.** Only the stated propositions S1 and S2 of pinned family063 are used, at fd4aeeb2…eeb. proof.md §§3–5 invoke no trace or spectral internals and no family122 reserved route. No perceived source inconsistency is exploited. Normal058 is explicitly excluded and unresolved.
- **History.** I ran a bounded search of canonical Markdown and JSON under frontier/, findings/, proposals/, reviews/ and notes/, excluding private/, inputs/ and context copies, for Mukai, pseudoindex, unsplit, 063 and Generalized-Mukai.
  - The only hits outside inventory screens are: geometry scout line 62 (catalogue mention), an r16 Mukai-pairing use in an unrelated K-theory argument, i19/i21 "unsplit" in a representation-theoretic sense, and the AGM063 ledger and tasks entries themselves.
  - There is no previously developed family063 chain and no prior AGM classification attempt.
  - This is not an exhaustive semantic audit of every historical note (details in reading-limits.md).
- **Literature.** Two standard web searches returned Fujita (arXiv 1409.8433), BCDD, Novelli–Occhetta, and Watanabe's special-range papers (arXiv 2403.14065, 2411.00379: ι=(n+1)/2, n/2, n−1, n−2 with ρ>1). These are search-only and were not read. None claimed the unrestricted AGM. That is search silence, not a priority certificate. The parent or manuscript gate should read the Watanabe papers before any manuscript states novelty relative to them, because they overlap the low-ρ part of the range.

## 6. Required and optional issues

**Required**

- **R1. Conditionality.** This SUBSTANTIAL verdict is void if the proof gate finds an unrepaired gap in §3 (saturation decomposition and the b=1 divisor step), §4 (support and dimension of the refined composition) or §5 (dominating-horizontal competitor). Any repair that adds a covering, contraction, rank or dimension hypothesis is a scope change and needs a fresh contribution review.
- **R2. Contribution attribution in any later manuscript.** The new contribution must be stated as the §§3–5 bridge only. The equality case belongs to family063. The template is Fujita Cor. 6.4/Prop. 5.3(b)/§4. The quotient is Kollár IV.4.16 via Fujita Thm. 3.2. The rank-one case is Dedieu–Höring Thm. 1.3. The result depends on the source's internal proposition S2 and not merely on the bound S1, and the manuscript must say so explicitly.
- **R3. Parametrised versus actual formulation.** Any claim to prove Fujita's Conjecture AGM^n_ρ, or AM^n_ρ through his Remark 1.5, must carry the §7 equivalence argument or an equivalent one. That argument uses S1. Without it, only the actual-invariant theorem is proved.
- **R4. Watanabe special-range papers.** Read them (§5) before any manuscript novelty sentence. Silence from a search cannot replace this.

**Optional**

- **O1.** proof.md §6 says the induction "supplies precisely" the premise of Prop. 5.3(b). Fujita's premise is the parametrised conjecture in dimension n+1−ι, which includes manifolds with ρ_Y'≥r. The proof of Prop. 5.3(b) uses it only for Y, where ρ_Y=r−1, and the larger-ρ cases are (P^1)^{n'} by S1 together with the §7 equivalence. One sentence would make this airtight.
- **O2.** Say explicitly that for unsplit families of degree <2i, the Chow families used in Fujita Defs. 2.3/3.1 parametrise only the irreducible curves. Then rc(W)-equivalence, which uses Chow families, is the same as the curve-chain relation used in §§3–5.
- **O3.** Cite the compatibility of correspondence composition with cycle class maps (for example Fulton Ch. 16/19) in §4, including the transpose convention for S_γ.
- **O4.** In §5, M is defined "with respect to a fixed ample divisor", but Fujita's minimality is in −K-degree. Use −K throughout.
- **O5.** The frozen author checkpoint.md says the campaign "remains at the parent's stated10/20". The current ledger (NEW-TEN line 963) says 11/20 after R033. This is stale text in a frozen file and not mathematical. The parent should note it at integration. I did not edit the author file.
- **O6.** The pinned tree also contains article.pdf for family063, which the author did not retrieve. The nine text blobs suffice for the stipulated statements. This is recorded only for completeness.

**Apparent mathematical issues.** None found at the level read for contribution purposes. The points in O1–O4 are presentation and interface precision, not gaps. This is not a proof-gate statement.

## 7. Identity

- Author anchors replayed: manifest 9afeca9b…5cb786, proof 285f5840…d7971c8c, scope 03a4861c…677081, checkpoint 3c7d6197…e6be6f. Author verify.py SHA is c9eb4a5d…fe814.
- The author verifier's positive run printed IDENTITY_PASS_ONLY with 44 files, 13 directories, 9 blobs, 2 PDFs and 20 contexts.
- The author context preprints-tree.json and upstream.json are byte-identical to repository sources/.
- Fresh downloads of both primary PDFs from the recorded URLs byte-matched the author receipts: Fujita d97b566d…bf92 and Dedieu–Höring d1e8594d…5b. The downloads were deleted afterwards and are not retained.
- This review's own verify.py and controls are described in checkpoint.md. Integrity is not mathematics.
