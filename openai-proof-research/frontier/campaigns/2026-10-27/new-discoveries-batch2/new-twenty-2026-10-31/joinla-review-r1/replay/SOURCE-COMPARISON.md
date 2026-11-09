# Bounded source and prior-art comparison for 365453

Investigator comparison, not independent novelty acceptance.

The exact claim is Conjecture 4.1 of Lau–Shiu, On local antimagic chromatic number of the join of two special families of graphs | II, Utilitas Mathematica 124 (2025),189–206, DOI 10.61091/um124-12. Both arXiv:2410.17674v1 and the actual published PDF state the even-component, odd-matching conjecture. Published p205 was rendered and inspected: outputs/published-conjecture.png. The current arXiv history lists only v1.

Source definitions distinguish aP₂ ∨ O_m from a(P₂ ∨ O_m). Our graph is two copies of 3P₂ ∨ O₂, not 6P₂ ∨ O₂. Degree multiset: twelve degree-three vertices, four degree-six vertices. The formal adjacency uses six matched pairs grouped three per component and two independent null vertices per component. Kernel certificates establish16 vertices,30 unique edges, adjacency completeness, symmetry, absence of loops, bijective labels and literal incidence sums.

Source machinery:
- Published Section 2 Theorems 2.1,2.3 and Sections3–4 construct the other parity cases using tables and merging groups with common sums. The conclusion specifically excludes even component count and odd matching size.
- This proof does not run the next entry of the table procedure or pad a published construction. It forbids every labeling, allowing the three colors to exchange roles between components.
- Source small displayed graphs and Theorem 2.3 concern even matching size. No target numerical table contradicted by the refutation was found.

Companion and cited primary-body comparisons:
- Lau–Shiu, Congressus Numerantium236 (2025),15–39. Section 2 Theorem 2.3 and Corollary 2.4 merge odd numbers of blocks of odd size, giving odd component counts. Section 3 Corollary 3.4 has the same odd-component restriction. Later G_{2n}(2r+1,2s+1) constructions use odd total matching counts and different component sizes.
- Lau–Shiu, Ars Combinatoria162 (2025),71–81. Theorems 2.1,2.4 modify odd total matching counts; their component/degree structures do not give this six-pair obstruction.
- arXiv:2404.18049, even-size matrix approach, Section 2: Theorem 2.4's rDF(2s) is bipartite with4s degree-two vertices per component. Our graph has triangles and no degree-two vertices. Matrix constructions and merging are not our nonexistence argument.
- arXiv:2403.16484, odd-size matrix approach, Theorems 2.1–2.5: fan/diamond-fan structures and odd block conditions; not our graph or obstruction.
- Chan–Lau–Shiu, CCO10(4)(2025),973–988, DOI10.22049/cco.2024.29032.1818. Theorems 1–3 concern stars and paths; Theorems 6–11 concern cycles. Actual Theorem 9 proof and preceding conditions read. χ_la(C₃⊔C₃)=4 is a relevant older parity precedent (Theorem 9 refers to Theorem 8). It does not directly subsume our graph: color-role counts (3,3,2) can permute across our components, and the mixed-role case requires the twelve-distinct-label argument. Local-antimagic chromatic number is not inherited monotonically from triangle subgraphs. Root should specifically assess whether this older counting framework makes the extension routine; no favorable significance ruling is presumed.

Public registries refreshed2026-11-04:
- OpenAI/math /commits/HEAD:4eaee87548250b2682affda7d05d947c05554bae, unchanged from brief. Cached complete manuscript catalogue searched by topic without relevant hit.
- Omega /commits/HEAD:d9880e9f2c329bb3db982f33791419d5d90126b9. Complete nontruncated D5 and Problems trees retrieved at subtree SHAs. No target-specific local-antimagic proof path located. This is a path screen, not reading every proof.
- Exact title, arXiv ID, formula fragments, graph parameters and counterexample terms searched on public web. Source and neighbouring constructions surfaced; no prior exact refutation located within this bounded screen. Numeric-ID searches mostly yielded irrelevant hits and provide no clearance.

Credited-family comparison:354228 is a constructive result on complete full t-ary trees;381805 is super edge-magic total labeling. Our graph is disconnected, triangle-containing, and resolves a different human conjecture. This distinction does not self-authorize another credited labeling family: root decides.

Dated byte hashes, URLs and HTTP statuses are in sources/*.receipt.json. One case-sensitive PDF URL returned404; the lowercase URL subsequently used was obtained from the publisher. No403/429/challenge retries, TLS bypasses or author contacts.
