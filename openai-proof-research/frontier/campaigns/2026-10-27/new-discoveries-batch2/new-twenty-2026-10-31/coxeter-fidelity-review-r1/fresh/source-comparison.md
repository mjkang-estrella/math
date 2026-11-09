# Primary-body comparison, 2026-11-01 UTC

Status: bounded comparison supports continued investigation; no novelty clearance or acceptance. Source bytes and successful HTTP receipts are in sources/. No denied registry route was retried.

## McKay 1977, On the spectral characterisation of trees

Read full extracted text, independently inspected scanned pp.223–224 (PDF pages5–6) because OCR omits displayed formulas. Lemma4.1 is a finite identity for bordered matrices made from A(T_i*) + k Δ*(T_i), k∈{-1,0,1}, with border vectors among 0,j,a*,q*. Theorem4.2 coalesces an arbitrary rooted S (at least2 vertices) with the two specific rooted16-vertex trees in Figure1. Its four parts give equal characteristic polynomials for (i) graphs and complements, (ii) line graphs and their complements, (iii) line graphs of complements and their complements, (iv) distance matrices and complement distance matrices. The proof applies Lemma2.2 and Theorem3.1 to those bordered identities; the line-graph case uses BᵀB=A(L(G))+2I and BBᵀ=A(G)+Δ(G). Lemma4.3 and Corollary4.4 establish the almost-all-trees consequence. Theorem5.3 instead reconstructs a tree from traces of ALL polynomials in noncommuting A and Δ (Algorithm5.4, leaf isolation).

None of these statements identifies geodesic growth with those polynomial spectra, or asserts that differing traces imply differing geodesic growth. Therefore Theorem5.3 supplies no refutation bridge. Theorem4.2 is exactly the spectral input to Ciobanu–Kolpakov Theorem3.2; their Lemma3.3 proves EQUAL growth for that construction. One cannot combine these statements to claim unequal growth. No claim that the underlying19-vertex graphs are themselves new is made.

## Godsil, Are Almost All Graphs Cospectral?, 9 November2007

The cited object is a slide deck, not a paper with numbered theorem statements. Read the text and inspect graph diagrams on PDF pages25 and28. Exact labels are slide titles: “Spectrum of a 0-Sum” (PDF22) gives φ(F)=φ(G)φ(H−v)+φ(G−v)φ(H)−tφ(G−v)φ(H−v); “Corollary” (PDF24) fixes the first rooted factor; “Another Pair” (PDF27) and “A Hint” (PDF28) provide the rooted-tree construction invoked as “page27” in Ciobanu–Kolpakov Theorem5.1. “Therefore…” (PDF35) states switching-related graphs are cospectral with cospectral complements; the preceding displayed conjugation uses K=(J−2I)/2 with K²=I and K1=1. These are spectral constructions, not geodesic-growth theorems. Labels and pages are retained rather than inventing theorem numbers.

Ciobanu–Kolpakov Theorem5.1 explicitly allows different line spectra. More strongly, its companion Lemma5.2 proves that every nontrivial common rooted extension of their particular S1,S2 differs at length10: the final proof counts 2 f_Geo^0(S_i)(8) deg_τ(0), with rooted counts8919523 and8919522 and positive root degree. Our recorded candidate agrees through17, including10. Thus their exact unequal-growth theorem does not directly generate this pair (even allowing relabelling). This is a full obstruction to that proposed bridge, not an inference from unfamiliar vertex labels or the use of computation.

## Godsil–McKay, Constructing cospectral graphs (1982/83)

Read §2.1–2.7, including the complete proof of Theorem2.2. An equitable partition C1,…,Ck,D permits local switching at half-neighbour columns. Q=diag(2J/|Ci|−I,I_D) satisfies Q²=I and conjugates adjacency and complement matrices. Theorem2.7 replaces congruent 0–1 attachment matrices A,B (AᵀA=BᵀB) via orthogonal conjugation. These are sufficient spectral constructions. Neither supplies RACG language counts or even generally preserves line spectra. Applicability to an underlying graph would not establish public unequal growth. No full-paper reading is claimed beyond the stated sections.

## Later relevant sources

Independently reread Ciobanu–Kolpakov v3 Conj1.3, Defs2.1–2.4, Thm3.2/Lem3.3 proof and Thm5.1/Lem5.2 proof. Existing source hash/version receipts from r10 are reused without alteration.

Antolin–Foniqi 2105.09751, Thm1.1/2.2 require link-regularity. Thm2.7 is the shortest-word forbidden-pair recognition theorem; it invokes graph-product normal forms rather than proving them afresh. Our graphs have degree1,2,3, so they fail link-regularity already for singleton cliques. The published general recognition theorem legitimately supports the ordinary proof, but cannot serve as an axiom in Lean.

Marjanski–Solon–Zheng–Zopff, Geodesic Growth of Numbered Graph Products, DOI10.46298/jgcc.2022.14.2.10019: fetched full primary PDF; read introductory statements, Thm4.9 and its proof, Lem4.10, and Thm5.14 and its proof (pp.2:8–2:15). Thm4.9 builds the general powered-clique automaton. Lem4.10 imports the graph-product shuffling normal form. Thm5.14 proves equal growth for equivalent LINK-REGULAR numbered graphs by a recurrence on power profiles. Thm6.4's statement also assumes link-regularity. Neither equality theorem applies to this irregular pair. The general FSA theorem is an existing tool, not a public refutation. Full proof of Thm6.4 not audited here.

## Scope and receipts

Live search on 2026-11-01 UTC covered exact title, author/conjecture, “geodesic growth” with “cospectral”, and later RACG growth. It located the above numbered-graph-product extension, not an independently verified refutation. No-hit results do not establish novelty. Current same-session registry receipts from r10 (head4eaee87548250b2682affda7d05d947c05554bae, fetched05:27–05:49UTC) and r11 access-limits (05:52UTC, Palomar403, inherited MathDB403) are reused with bounded scope. The root registry tree was truncated, the separate preprints subtree complete; these are path searches, not body-wide clearance. No acceptance until independent novelty/significance review and source-faithful full Lean endpoint.
