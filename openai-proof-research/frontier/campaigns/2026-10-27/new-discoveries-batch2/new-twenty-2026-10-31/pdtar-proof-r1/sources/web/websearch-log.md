# Web search log (2026-11-03 UTC, lane pdtar-proof-r1)

Search-engine results are untrusted secondary evidence. Primary HTTP fetches are recorded in `receipts.txt`.

## Queries

1. **"power domination TAR reconfiguration graph complete bipartite K_{s,t} unique conjecture proof"** (extended). Returned only the source (arXiv:2201.01798 and the La Matematica version), the survey arXiv:2406.05509, and Bong et al. (arXiv:2205.09668). No proof of the K_{s,t} conjecture.
2. **"\"power domination\" \"reconfiguration\" \"complete bipartite\" unique TAR graph 2025"** (standard). Returned the source, Hogben's Sage PDFs on aimath.org and the survey. The only 2025 hit (Messinger–Pipes, domination TARS pancyclicity) is unrelated.
3. **"\"Power Domination Reconfiguration\" La Matematica 2026 conjecture K_{s,t} unique \"s\\ne 2\""** (extended). Returned the publication record and a Swarthmore repository copy (CC-BY). Neither snippet shows a resolution.
4. **"\"power domination\" TAR graph \"K_{p,q}\" unique Hogben Curtis Flagg 2026"** (standard). No 2026 work found.
5. **"arXiv 2025 2026 \"power dominating sets\" same family \"complete bipartite\" …"** (standard). No relevant hit.
6. **Query 6** (extended, restricted to link.springer.com). The engine's index of the La Matematica page (10.1007/s44007-025-00187-5) reports:
   - Theorem 3.16 (K_{1,t});
   - Proposition 3.24 (K_{3,3});
   - **Conjecture 3.25: "PD^TAR(K_{s,t}) is unique if and only if s ≠ 2 and t ≠ 2"**, still stated as a conjecture in the published version.

   This is secondary evidence: the page itself was a JS challenge for curl.

## Primary-source access outcomes

| Source | Outcome |
|---|---|
| arXiv abs 2201.01798 | 200; v1 only |
| arXiv abs 2406.05509 | 200; v2 dated 2025-09-28, the cached TeX matches v2 and still lists the conjecture as open |
| link.springer.com article page | 200, but the body is a JavaScript client challenge. Not retried, per policy |
| Swarthmore viewcontent PDF | 403. Not retried |
| Crossref and OpenAlex APIs | 200 |
| arXiv author page `hogben_l_1` | 404 |

Crossref and OpenAlex show the following:

- Published 2026-01-13 in La Matematica 5, article 8, under CC-BY.
- One citing work: the survey's journal version (La Matematica 2026, doi 10.1007/s44007-026-00207-y).
- Hogben's works from 2024 onward contain no PD-TAR K_{s,t} resolution.
- The "Determining a graph from its reconfiguration graph" hit (EJC 2026, arXiv:2504.19783) concerns colouring and independent-set reconfiguration and is unrelated.

The arXiv search API and ScienceDirect were never used.
