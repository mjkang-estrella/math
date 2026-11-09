# MathDB 365710: focused novelty review

2026-11-01 UTC. **HOLD**, not acceptance. No subsumer or routine full-scope bridge established. Zero credit; campaign remains 6/20 beyond 39. Root alone accepts. Lean completion and fidelity PASS are inherited from the supplied review, not re-audited here.

The target is the maximum of the unordered-pair squared degree difference sum over all connected triangle-free n-vertex graphs. The candidate uses D = nm - M1, its one-edge-triple interpretation, the strict non-complete-bipartite gap D >= n - 2, and discrete bracketing. The gap, rather than the invariant identity, remains the decisive novelty question.

## N1: Bell 1992 — still open

The original body remains unread. OpenAlex returns only the already denied publisher PDF. I did not retry it or CORE. The separately permitted publisher HTML route returned 403 and was stopped. Bell-citing metadata was screened (first 50 results only). No lawful Bell copy or numbered, sufficiently complete restatement of all his theorems was found.

The most precise accessible restatement remains **Zhou 2004, Remark 4, p.115**, re-read visually here. It defines the quasi-clique C_n^m from m = binomial(d,2) + t, 0 <= t < d, and its complementary quasi-star S_n^m. It attributes fixed-edge M1 upper bounds to reference [12] (Bell), using C_n^m in the high-edge regime m > binomial(n,2)/2 + n/2 and S_n^m in the low-edge regime m < binomial(n,2)/2 - n/2. These are unrestricted hypotheses, not a triangle-free stability theorem. Zhou's immediately following Theorem 5 separately proves M1 <= nm for triangle-free graphs. This does not show that Bell lacks further restricted-class results.

**Elphick–Wocjan 2014, p.52**, also attributes unrestricted variance and spectral-irregularity extremizers and incomparability examples to Bell. It gives no Bell theorem numbers or restricted triangle-free maximum there. These restatements support the unrestricted interpretation of the cited Bell results but do not clear the entire unread paper. Bell could still contain a relevant bipartite or triangle-free result; exclusion would be unjustified.

## N2: origin papers — narrowed, not cleared

All three proposed arXiv PDFs returned 200. None is the cited origin paper or an established equivalent manuscript:

* **1904.05053v1**, Ali–Réti, *Two Irregularity Measures Possessing High Discriminatory Ability*: read introduction/Table 1 and Sections 2–3 theorem/proof text. It introduces IRA/IRB from equal-degree-pair counts N0. Proposition 2.2 concerns their antiregular extremizers; Lemma 2.4 and Proposition 2.5 bound N0 and IRA/IRB; Section 3 rewrites absolute total irregularity via the Gini index. This is not the solo Réti paper in AMC 344–345, 107–115. No equivalence to that paper was established.
* **2211.06744v1**, Ghalavand–Réti–Milovanović–Ashrafi, *Graph Irregularity Characterization with Particular Regard to Bidegreed Graphs*: read Sections 1–4 and Proposition 14/proof; screened the remaining theorem labels and references. It studies S and Var, not a fixed-n triangle-free sigma_t maximum. Theorem 2 bounds Var by (Delta-delta)S/(2n) and by (Delta-delta)^2/4; Propositions 7–8 concern bidegreed balance; Proposition 11 requires a dominating graph. A connected triangle-free graph with a universal vertex is a star: all other vertices are independent and adjacent to it. Thus Proposition 11's domain does not cover the target's non-star graphs. OpenAlex associates this manuscript with DOI 10.66224/ijmsi.21.1.85, not the Réti origin DOI.
* **2501.01538v1**, Ali–Dimitrov–Réti–Albalahi–Hamza, *Bounds and Optimal Results for the Total Irregularity Measure*: read definition, Section 3.1 maximum results through Theorem 5, and Section 4 opening sigma comparison. Its invariant is sum |d_u-d_v|, not sum (d_u-d_v)^2. Theorem 4's unrestricted antiregular maximizers and edge-sigma comparisons therefore do not resolve this target. It cites D–S 2023 in reference [28]; citation is not republication of its body.

The actual origin papers remain unread: Réti, DOI **10.1016/j.amc.2018.10.010** (2019 volume; online 2018), and Dimitrov–Stevanović, DOI **10.1016/j.amc.2022.127709** (2023 volume; online 2022). Current OpenAlex results expose only publisher locations for them. Two arXiv metadata searches (inverse-irregularity phrase; both authors and irregularity) found no entries. A candidate institutional author-home URL returned 404; the public ORCID person record exposed no manuscript/homepage route. These are bounded failed discovery attempts, not proof of no preprint. ArXiv `all:` queries search indexed fields, not arbitrary PDF full text.

Dimitrov's coauthorship of both the 2023 origin and the later conjecture makes a direct conspicuous subsumption less plausible. It cannot substitute for reading either origin body. N2 remains material.

## N3: strict Zagreb deficit — narrowed, still unresolved

Targeted OpenAlex searches covered triangle-free Zagreb bounds, complete-bipartite bounds, and induced one-edge triples; arXiv queries covered triangle-free with Zagreb/variance/irregularity. Results included unrelated geographic Zagreb and probabilistic variance items. Bing responses were irrelevant first-word results, and Google served a redirect/interstitial: neither is negative novelty evidence.

Two actual relevant bodies were compared:

* **Elphick–Wocjan, New measures of graph irregularity (2014), Section 4, Theorem 4.1(i), pp.56–58**, including its proof and equality remarks. With nu = nM1/(4m^2), substituting clique number 2 into 2m <= (omega-1)n^2/(omega nu) gives exactly M1 <= nm. The proof uses Moon–Moser clique counts, including nm + 3t >= M1. It supplies no connected n-2 deficit in the passages read. Equality-only exclusion gives at best integer D >= 1, not the candidate's D >= n-2. For example, at n=10, completing the square with D >= 1 gives only sigma_t <= 625-10 = 615, whereas the best complete bipartite value is 576 (parts 1/9 or 2/8). Thus that argument does not settle even this order; additional structure would be needed.

* **Vaidya–Chang, arXiv:2409.06081v1**, read Section 3 Theorem 3.2/Corollary 3.4 and relevant Section 4 statements/proof portions. Corollary 3.4(1), alpha=2, is M1 <= 2m(Delta+delta)-n delta Delta. On K_(2,6) minus one edge, a connected triangle-free non-complete-bipartite graph, n=8, m=11, delta=1, Delta=6. This upper bound is 106; the desired nm-(n-2) is 82, which is its actual M1 (degrees 6,5,2,2,2,2,2,1). Thus this bound alone does not supply the strict gap. The triangle/quadrangle-free Section 4 bounds concern 2-distance degrees and impose the extra quadrangle exclusion, absent from the target.

The retrieved MATCH paper *Irregularity of Graphs* was screened at pp.371–373 and its references. It studies edge-absolute Albertson irregularity. Its references to bipartite/triangle-free maxima therefore do not themselves identify squared all-pair maxima. The remainder was not read and is not globally cleared. The 2025 survey also leaves the absolute/squared distinction essential.

No published D >= n-2 bound, equivalent induced-triple bound, or full triangle-free variance maximum was established. The searches are too limited to clear the specialist literature. Discovery of such a bound could make this a routine corollary through the already short integer-bracketing argument; this remains a live objection.

## Disposition and receipts

Retain HOLD, with no worldwide-first or acceptance claim. The useful advance is rejecting the three arXiv candidates as substitutes for the origin bodies and comparing two further actual bound bodies. No original objection is cleared. Decisive next evidence is a lawful Bell/origin body or a precise strict-gap theorem with hypotheses and proof.

`receipts/*.json` records UTC time, exact URL, status, final URL, bytes and actual SHA-256 for each HTTP response, including failures. `downloads/` preserves received bodies and text extractions. `receipts/manifest.json` binds local evidence and read-only inputs used. No forbidden route was retried. No agents, git, ledgers, tabs, external messages, publication or uploads were used. Registry checks from r1 were not repeated: this pass is a bounded comparison, not a fresh acceptance audit. All launched fetch processes finished; no background jobs remain. HTTP work was limited to two workers/two-CPU affinity, CPU 120 seconds and 6 GiB address space, with 22-second request timeouts. One render invocation failed from an integer command argument and was corrected locally; source evidence was unaffected.
