# Fresh full-source target: Xie–Xu 2-matroid ultra-log-concavity

Status: UNRESOLVED. No full proof, source counterexample, formal claim, nomination or acceptance. Root owns eligibility and acceptance. This lane does not change campaign counts.

## Actual source and quantifiers

Primary: Yan-Ting Xie and Shou-Jun Xu, *Ultra log-concavity and real-rootedness of dependence polynomials*, Electronic Journal of Combinatorics 33(4) (2026), #P4.9, DOI https://doi.org/10.37236/13310. The actual downloaded published PDF has 20 pages; its final source statements are on printed pp17–19. This differs from the arXiv metadata's 16-page description. The latest observed arXiv revision is https://arxiv.org/html/2408.09152v2, 10 October 2026; actual published body and v2 final-section bodies were read and compared. Publication landing page gives 9 October 2026. There is no forthcoming-resolution announcement located in the read source body or bounded follow-up searches.

Full selected target: published Conjecture17(iii), corresponding to arXiv v2 Conjecture4.4(iii). Let E=[n], and let I be a nonempty downward-closed family of subsets of E. Assume that whenever S,T belong to I and |T|>=|S|+2, there exists x in T\S with S union {x} in I. This is the authors' additive-gap definition of a 2-matroid, NOT intersection of two matroids. Write i_k=#{S in I:|S|=k}. For every such finite system and every 1<=k<=n-1 the proposed inequality is

    k(n-k) i_k^2 >= (k+1)(n-k+1) i_(k-1) i_(k+1).

The full universal statement is targeted, not a selected rank/parameter instance. Clauses(i) and(ii), separately, are not claimed solved. No alteration of their normalization or endpoints is used.

The narrower graph question is published Conjecture14 / arXiv v2 Conjecture4.1: for EVERY finite simple graph, its dependent-set counts d_k satisfy the same all-index inequality. Here dependent means its induced subgraph has an edge. The actual coefficient definition is D(G,x)=(1+x)^n-I(G,x). The source's co-dependent family {S:E\S contains an edge} is a 2-matroid, so the selected stronger question includes the entire graph target. Graphs without edges have zero dependent counts and trivially satisfy the inequality. No computational case is being counted.

## Economical early proof/subsumption screen

Read the assigned rules, ledger, NEXT and prior-campaign-context; read the prior discovery-lane summaries including r26–29. None supplies this target. All explicitly excluded families remain excluded. Prior diagnostic conclusions were not adopted as mathematical lemmas.

The actual current v2 and journal bodies retain both selected conjectures. Their already-proved special graph classes and real-rooted classification are credited, not treated as discoveries. In particular, two disjoint edges is ALREADY a source-known real-rooted graph case.

Closest classical body: Anari–Liu–Oveis Gharan–Vinzant, https://arxiv.org/pdf/1811.01600v1, actual Theorem1.2, Definition1.3 and homogenization construction pp1–2 read. They prove the full ULC theorem for ordinary matroids via complete log-concavity of the multivariate homogenized independent-set polynomial. Ordinary matroids require augmentation at a size difference of ONE; this is strictly stronger than the selected size-difference-TWO hypothesis. Therefore their theorem does not directly apply. The exact obstruction below rules out simply repeating their multivariate conclusion for all source 2-matroids.

Horrocks2002 DOI https://doi.org/10.1006/jctb.2001.2077 produced a publisher landing page only; the actual ScienceDirect body returned403 and was not retried. Its ordinary-log-concavity conclusion is explicitly credited in the source, but an independent full-body proof comparison is a remaining gap. Read the related actual Horrocks2000 *Doubly dependent sets in graphs*, https://ajc.maths.uq.edu.au/pdf/22/ocr-ajc-v22-p105.pdf, Section3 Theorems3.1–3.3 and proofs. Sperner/unimodality/adjacent-rank matching are weaker than the required normalized consecutive-rank product inequality. No complete stronger subsumption bridge was found there; this is not an exhaustive Horrocks literature audit.

Important early public counterpart: Alex Chengyu Li's public primary project page https://crabresearch.com/research/augmentation-gap-log-concavity?lang=en describes a September2026 refutation of the OLD rank-dependent Xie–Xu Conjecture4.8. Its reported construction has augmentation parameter THREE and rank4; this does not refute the surviving parameter-TWO conjecture. Source page metadata changed between indexed and current responses: current read lists SSRN, revised18September2026, DOI10.2139/ssrn.7434141; the indexed result listed Zenodo/revised8September. The linked body was inaccessible, and direct project/SSRN requests returned403. No alternate-host bypass or repeated challenge requests. Accordingly this is a material UNREAD-BODY prior-art gap, not definitive clearance for Conjecture17. No old rank-dependent extension is nominated or rediscovered.

## Ordinary-proof attack and exact falsifier

The attempted universal mechanism was: replace the ordinary-matroid hypothesis in the classical multivariate homogenization argument with the source's 2-augmentation axiom, then use its bivariate specialization to obtain all inequalities. This proposed mechanism fails, already for a source graph.

Take E={1,2,3,4}, G with edges {1,2} and {3,4}. Its co-dependent family is

    I = P({1,2}) union P({3,4}).

Indeed E\S contains edge {1,2} exactly when S is a subset of {3,4}, and vice versa. This establishes the actual graph-to-family bridge independently. The 2-augmentation axiom holds: all independent sets have size<=2; only an empty S and a two-element T require checking, and either singleton of T works. This is not an ordinary matroid: S={1},T={3,4} give a one-step augmentation failure.

Its rank sequence is (1,4,2,0,0), which DOES satisfy the source ULC claim. The graph's dependent sequence is its reverse, (0,0,2,4,1); no source violation arises.

The literal multivariate homogenization used by the classical method is

    F(y,x)=y^4+y^3(x1+x2+x3+x4)+y^2(x1*x2+x3*x4).

Its nonnegative coordinate derivative Q=partial_y^2 F equals

    Q=12*y^2+6*y*(x1+x2+x3+x4)+2*(x1*x2+x3*x4).

On the positive line (y,x1,x2,x3,x4)=(1,1+t,1+t,1-t,1-t), |t|<1, this is exactly 40+4*t^2. Hence Q at t=+1/2 and t=-1/2 is41, while its midpoint value is40. Log-concavity would require 40>=sqrt(41*41)=41, which is false. Equivalently (log Q)'' at zero is1/5>0. Thus F is not completely log-concave on the positive orthant. This is a fully ordinary exact proof of a METHOD OBSTRUCTION, not of the source conjecture's failure and not a new theorem nomination.

A bivariate-only proof could still work; failure of multivariate CLC does not rule it out. Merely checking each bivariate derivative's quadratic determinant restates the desired coefficient inequality and is not an independent proof mechanism. Truncation preserves downward closure and the size-two augmentation axiom, so a uniform top-rank inequality would suffice after truncating at each k+1. No such top-rank inequality was obtained. Counting possible extensions alone has not supplied the required weighted second-moment bound.

## Exact bounded checks

Run `bash run-checks.sh`. `check.py` uses integers only and hard512MiB address space,40CPU-second,55-second internal wall alarm, with an outer60-second timeout and BLAS threads1. No Lean was run. It constructs all Boolean-lattice ideals recursively via the unique sections I1 subset I0; no uncapped enumeration occurs. For n=1,...,5 it finds respectively3,6,20,168,7581 ideals; respectively2,5,19,163,6715 nonempty systems satisfy the full 2-augmentation predicate. All their literal ULC inequalities pass. Independently it enumerates all labelled nonempty-edge graphs through n6 (33861 total), counts dependent subsets by a vertex-removal recurrence, and checks every coefficient inequality. No failure occurs. The route witness is checked against the actual graph-complement definition and exact polynomial arithmetic.

These are finite diagnostics only. No infinite/all-n result, minimality claim, new source-case theorem or credit follows. Source already proves the witness graph. Expanding enumeration is not the missing proof step.

## Current public-registry screen and limits

Ordinary public HTTP only; no browser tabs or GitHubAPI calls. All retrieval UTC/status/URL/hash entries are in http.json. Current public root HTML reports:

- OpenAI math main:7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a, matching the saved head associated with the complete13578-entry preprint tree.
- AIM:8729eab98bafe409b66c5e39253bf56569a62327, matching the saved complete3541-entry tree.
- Count:dbf673741a54c7dc9d88a6aec0e8148a538f4a3a, matching the saved complete183-entry tree.
- Omega default branch dev:25645e81f219c1ee67cf1b8e07d6235fe9182fb0; explicit main:d7af67136d4478875778ac6e75eb5fbb8b3693a5. These are ROOT HTML OBSERVATIONS ONLY. They do not establish ancestry relative to root's previous b424f1df review or a complete delta/tree screen. Saved r22 scoped D5/Problems trees have12478/1541 entries; all paths screened but current complete Omega coverage remains OPEN.

registry-screen.json preserves exact tree inputs and broad matches. Broad lexical matches such as independent-rate or matroid-matching paths are NOT matching actual proof claims; no such path is called a subsumer without reading its mathematical body. No exact dependence-polynomial/2-matroid endpoint path was identified. Fresh public exact-title, author-follow-up, conjecture and registry-index searches located the old Li counterpart above but no verified full parameter-two solution. Absence of path/search results is not novelty evidence.

Retrieval mistakes are preserved: a first unrelated teorth/analysis root and two guessed registry URLs were read/404 before the correct repository identities were recovered from saved provenance. They contribute ZERO target coverage. Initial local HTML extraction failed because bs4 is unavailable; stdlib extraction succeeded. One guessed arXiv v4 for the classical source returned404; its actual history shows only v1, which was then downloaded and body-read. No source/fetch failure is erased.

## Strongest substantive objection and handback

There is NO full eligible discovery. The substantial-looking new item here is only a counterexample to an overstrong classical proof strategy; such helpers/route obstructions are explicitly uncredited. The full rank inequality needs a genuinely different mechanism or an actual in-scope 2-matroid witness. Moreover, the closest public Li paper body and Horrocks2002 body remain unread, and Omega current complete coverage is missing. Neither stale empty MathDB solutions nor finite tests resolves these objections. No independent eligibility review or large Lean investment is warranted on this packet yet. No PROOF.md is written, because the ordinary SOURCE proof remains absent.
