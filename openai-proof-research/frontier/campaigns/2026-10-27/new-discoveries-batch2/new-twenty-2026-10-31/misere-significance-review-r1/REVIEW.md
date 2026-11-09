# Independent contribution and prior-art review: MathDB 320321

Review date: 2026-10-31 America/Los_Angeles / 2026-11-01 UTC.

**Bounded prior-art verdict: FAIL for new-discovery eligibility. Mathematical-significance verdict: FAIL under this campaign's exclusion of routine corollaries. Recommended credit: 0.** These findings do not challenge the mathematical correctness, definite-clause fidelity, or Lean checks previously passed. There is a positive prior-art obstruction to novelty, rather than a HOLD based on incomplete search: Allen's precise nontransitivity conclusion follows by a short reduction from Siegel's published failure of invariance of the impartial mate construction.

The particular triple `star, node[node[zero,star]], zero` was not located in an earlier source. Its possible novelty as an especially small explicit certificate is a narrower claim than a new mathematically significant solution. No minimality theorem or substantive strengthening beyond the known consequence is submitted. No count, publication, or candidate edit was performed.

## Exact endpoint and source comparison

The reviewed relation on finite impartial **positions** is

    A(a,b) iff o^-(b + a°) = P.

For these positions this is exactly Left winning moving second, and also Right winning moving second. The source's adjoint restricted to impartial positions is precisely Conway's mate: 0° = star and the mate of a nonterminal position is the set of mates of its options. This identification is by the recursive definitions, not by normal-play equivalence or an assumed quotient operation.

Allen, *An Investigation of Partizan Misere Games*, arXiv:1008.4109v1, Definition 6.3.1 and Section 6.3, printed pp.128–130; Conjecture 6.5.1, p.131; future work, p.202, were read in the actual cached PDF/text. PDF pp.144 and 146 were independently rendered and inspected. In Example 6.3.3 the triple is star, **1**, **rho-bar**. The bar is visible in the PDF and is lost in some extracted text; 1 is the partizan position {0 | }, and rho-bar is its adjoint. Thus this is not the candidate's impartial triple. The same source concludes that partizan Left-second, Right-second, and second-player versions fail. This is not itself an impartial obstruction.

Section 6.4 uses conjugation and first-player conditions in a restricted ab3 setting. Examples 6.4.1–6.4.3 do not assert the same adjoint/second-player relation. Section 6.5 explicitly returns to Section 6.3 and reports an unsuccessful search for an all-impartial triple. The new certificate really answers that failed search. The future-work passage allows an unspecified change of winning condition; it does not specify a second exact relation. The certificate does not settle those alternatives or the general existence of a misère category.

I do not classify the candidate as a routine transformation of Example 6.3.3. For example, the natural recursive symmetrization replacing the two option sets by their union sends its triple to S,S,U, with S={0} and U={0,S}. Since the first two positions now coincide, this cannot witness nontransitivity. The source's asymmetric winning-strategy argument therefore does not transport by this obvious operation. This observation is not a proof that every conceivable reduction from that example fails. The decisive exclusion below comes from later **impartial** theory instead.

## Positive prior art and explicit reduction

Aaron N. Siegel, *On the Structure of Misère Impartial Games*, [arXiv:2012.08554v1](https://arxiv.org/pdf/2012.08554v1), submitted **15 December 2020**, Section 2, printed pp.2–5, and Section 3, pp.5–6, are decisive. The same result remains in [v2](https://arxiv.org/pdf/2012.08554v2), revised **3 September 2021**, Section 3, p.5. Both PDF bodies were retrieved; v2 p.5 was rendered to check the notation. Section 3's example explicitly supplies a finite impartial form H equal to 0 with H's mate unequal to the mate of 0. Its displayed conclusion is H=0 but H^- != 1. The examples use the paper's sharps/subscripts notation; refer to the PDF for that notation rather than interpreting plain extracted `2## 0` as an integer or concatenated option list.

Here equality means indistinguishability in **all finite impartial misère contexts**, as defined on p.2, not normal-play equality and not equality against all partizan contexts. Definition 2.5 (p.4) is the same recursive mate used here; Proposition 2.6 gives o^-(G+G^-)=P. Consequently the objects, sum, terminal convention, adjoint, and outcome semantics all agree with the candidate's restriction.

Here is the complete reduction, independently derived for this review. Write x~y for that contextual equality; this is auxiliary notation on forms, not a change of the conjecture's object domain.

1. If x~y, then A(x,y) and A(y,x). Indeed y+x° has the same outcome as x+x°, which is P by the mate theorem; interchange x and y for the other arrow.
2. If A were transitive, those mutual arrows would imply, for every finite impartial t,

       A(x,t) iff A(y,t).

   One direction composes y->x with x->t; the other composes x->y with y->t.
3. Unpacking this equivalence gives

       o^-(t+x°)=P iff o^-(t+y°)=P  for every t.

   Every finite impartial sum is either N or P. Thus its full outcome agrees in every context, so x°~y°.
4. Hence transitivity would force **mate invariance under contextual equality**. Siegel's explicit H~0 but H° not~ 0° contradicts precisely this consequence. Therefore A is not transitive.

For an explicit conversion of the prior separating context into a counterexample, choose t distinguishing H° from 0°; such a finite impartial t exists by the definition of their inequality. We already have H->0 and 0->H. If A(H,t) holds and A(0,t) fails, the triple (0,H,t) violates transitivity. In the opposite case, (H,0,t) does. These exhaust the two possible differing outcomes. This is a direct reduction from the published same-object example, not an inference from a vague failure of inverses, cancellativity, or category terminology.

Siegel does not label this observation a refutation of Allen Conjecture 6.5.1 in the inspected passage. That is not necessary to establish routine subsumption. The endpoint already follows from his explicit example and the standard mate theorem with no additional game-theoretic construction. The candidate supplies a different, smaller-looking constructive witness; no claim that the **same** triple is printed there is made. Siegel Section 4 also already lists the form {nim-heap-2}, the candidate's middle position (his `2#`), among early impartial games. Prior occurrence of that individual game alone would not establish prior occurrence of the obstruction.

Chronology: Allen's arXiv v1 dates to 24 August 2010; the thesis itself carries July 2009. The decisive Siegel example is present already in the actual **2020 v1**, pp.5–6, not merely in a later abstract or newly indexed page. It predates the present 2026 campaign by years. The paper's introduction attributes some work to 2006–07; I do not infer public availability at that earlier date. No chronology comparison with our own 39 results is needed for this external subsumer.

## Other inspected primary literature and bounded negative findings

The following checks provide context; none is used as an absence certificate.

- Siegel, *Misère canonical forms of partizan games*, GONC4 (2015), pp.225–238: Sections 2–3 and 7–8 were read. Definition 3.2 and Proposition 3.3 (p.228) supply the adjoint and self-pairing outcome. Proposition 7.2 distinguishes impartial-context equality from unrestricted partizan equality. These facts alone do not assert nontransitivity. The preprint is arXiv:math/0703565; the inspected typeset PDF is a later publication, so a 2015 date does not date the construction's origin.
- Allen, *Peeking at partizan misère quotients*, GONC4 (2015): introduction and final open questions were read, including question (6), printed p.11. It asks broadly about applying combinatorial game categories to misère play, cites the thesis and Cockett–Cruttwell–Saff, and does not supply this impartial triple or supersede the Section 3 reduction above.
- Plambeck–Siegel, *Misère quotients for impartial games*, accessible IAS manuscript: quotient definitions and the generalized mex/interpolation setting were inspected. These compare outcome partitions on closed sets; they are not an assertion that an individual mate acts as a negative giving composition. No particular witness was located in this bounded inspection; a full theorem-by-theorem subsumption audit of that paper is not claimed.
- Larsson–Nowakowski–Santos, *Absolute combinatorial game theory*, GONC6, actual PDF: adjoint/saturation passages, including Definition 44, were inspected. Those construct test games in universes and do not identify the individual mate with a compositional inverse. No matching arrow assertion was found in those passages.
- Davies–Milley, *Order and inverses in the monoid of misère blocking games*, published 20 April 2026: search-indexed author/publisher material points to Definition 3.9 and the classical adjoint theorem. Direct PDF retrieval returned 202 with an empty body; the article page then required a robot check. No bypass or retry followed, and its full body is **not** cleared or relied on.
- Dorbec–Renault–Siegel–Sopena, *Dicots, and a taxonomic ranking for misère games*, DOI 10.1016/j.jcta.2014.10.006: the indexed primary passage identifies the same adjoint/self-pairing theorem, but the LaBRI author PDF was inaccessible. The DOI tool could not follow its publisher redirect. An additional guessed publisher PII request returned 403 and is not treated as the target article. The complete body is **not** claimed inspected.
- Siegel's 2013 book, Chapter V, especially the mate discussion, remains an unread full-body source: the AMS page returned 403. A third-party indexed text was a discovery lead only, not a proof dependency. The accessible 2020/2021 primary paper explicitly states the needed results and provides the decisive example. Access to the book is consequently unnecessary for this rejection; it might establish still earlier public chronology.

Exact URLs, retrieval times, HTTP failures and byte hashes are in `http-evidence*.json`; downloaded PDFs and extracted texts are retained here. `search-log.json` records the thematic and citing-work searches. Search engines' misleading relative publication dates were not used as bibliographic dates. This is a targeted later-literature and citing-work investigation, not an exhaustive citation graph, MathSciNet or zbMATH audit.

## Current registries and previous-result exclusions

Fresh public HTTP checks on 2026-11-01 UTC retrieved OpenAI math HEAD **4eaee87548250b2682affda7d05d947c05554bae**, commit timestamp **2026-10-30T00:35:35Z**. The immutable CONTENTS.md and complete recursive **preprints subtree** (13,578 entries, `truncated=false`) were checked. No misère/impartial/320321 counterpart was identified. Hits for adjoint concern other subjects; game titles concern Unique Games and algorithmic game problems, not this relation. This is a catalogue/path screen, not a claim to have audited every proof body. No relevant OpenAI manuscript was identified for a body comparison; the positive subsumer is Siegel's actual primary body.

Fresh proofsearch.org, prove2.me, and qed.bot pages were saved and screened for misere/misère, impartial, 320321, 1008.4109 and adjoint. No corresponding entry was found in the retrieved pages. These are landing-page/server-delivered content checks, not every record or their complete databases. Current MathDB histories are inaccessible; the cached record cannot certify current unsolved status. The inherited MathDB403 limit is retained without another request. Palomar's API and browse-index403 limits, documented in `../lane-3/SUMMARY.md` and `live-sources.json`, are likewise retained without retry, alternate data endpoint or bypass. Search-indexed Palomar material is not substituted for live registry clearance. These gaps cannot rescue novelty in the face of the positive external subsumer and do not require a HOLD here.

The ancestor ledger and prior-campaign-context list the earlier 39 credited results. No credited mate/adjoint/impartial-composition family was identified there. Earlier odd randomized subtraction and Bernoulli-game results concern different objects and endpoints. None of our own publications is used as independent external prior art, nor is any repeated here as credit.

## Contribution assessment and consequence

The exact counterexample is a legitimate mathematical answer to Allen's definite clause. Its consequence is a hom-existence obstruction: if hom(a,b) consists of the proposed second-player winning strategies, there can be nonempty hom(a,b) and hom(b,c) with empty hom(a,c). Therefore **no composition law on those hom-sets** can turn the full collection of finite impartial positions into a category. Reflexivity from the mate theorem does not suffice. The example also covers Left-second/Right-second/second-player readings on these impartial sums.

It does not prohibit other sums, negatives, restrictions of objects, changed winning conditions, taxons, or other game categories. It establishes no theorem of nonexistence for all misère categories and no statement on the well-definedness of an adjoint arrow on a quotient. Contextual equality was used only to derive the prior-art reduction over positions.

Its proof being tiny is not the reason for FAIL. The reason is the displayed reduction from an earlier same-object result to the exact submitted endpoint. Under the campaign's explicit exclusion of routine corollaries and mere formalizations, the Lean certificate and especially small witness do not merit another new-discovery count. Preserve the checked counterexample as an uncredited explicit illustration, with the Siegel citation added in any future account. A new significance case would need a materially stronger result (for example a genuine classification or proved sharp minimal obstruction with independent interest) and its own novelty assessment; it would not retroactively make this endpoint new.

No further missing source is decisive for the present **FAIL/0** recommendation. A full book or inaccessible registry check could supply more prior art, but cannot undo the proved subsumption. No worldwide-priority guarantee, exhaustive literature-clearance claim, or acceptance/count update is made.

## Integrity

`hash-verification.json` records all 64 protected candidate, source and fidelity-review files unchanged against the beginning-of-review snapshot. Every entry in the candidate manifest matches, including Counterexample.lean SHA-256 `c52af1a0a74df6ff5dc9780cb4fece600a565fe5f6f105d881691c4c92520713` and the frozen archive `dfaa89e9c941c045399731643fa89de1609209a93ca88ab65d2ef83f38263c1e`. The source PDF SHA-256 is `6c2d126802080ea4145ecbb77f79ee161ee8b94a78c4558ee9ff1ddf399ddd3d`.

Decisive prior PDF hashes: Siegel v1 `135be37772613913253ef167b2eb2dd28fa737ff0cc0f4a3ca07e0c4ede28c91`; v2 `aed302eb97da83963e791488a80dd6a0154ebe9f88b79cd039a5b13f4f81cb46`. This review did not rerun Lean or modify the earlier proof verdicts. All authored/downloaded artifacts are confined to this assigned review directory. No delegation, git operation, browser tab, external post or shared-ledger change occurred.
