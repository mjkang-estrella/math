# Statement correspondence

MathDB 350452 literal (cached `expanded-corpus-r209/raw/350452.jsonl`, statement SHA-256 202a3342692ab879eb785af329027d1d30ee0997836e07b9f02383649d316436):

> The path P_n is not an IR-graph for each n ≥ 3, and the cycle C_n is not an IR-graph for each n ≥ 5.

`Conjecture` is exactly the conjunction of the two quantified claims, using Mathlib `pathGraph n` and `cycleGraph n`. `conjecture_false : ¬ Conjecture` refutes it using n = 9 in the first conjunct. This does not claim a refutation of the cycle assertion alone.

Primary definition source: Mynhardt–Roux, *Irredundance Graphs*, arXiv:1812.03382v3, Sections 1.1 and 1.2. Cached source:
`../expanded-corpus-r209/sources/src-1812.03382-20261105T100524638204/extracted/Irredundance_Graphs.tex`.
The following are exact TeX excerpts (line wrapping normalized only):

> A $D$-\emph{private neighbour }of $v\in D$ is a vertex $v^{\prime}$ that is dominated by $v$ but by no vertex in $D-\{v\}$.

> $\operatorname{PN}(v,D)=N[v]-N[D-\{v\}]$.

> A set $D\subseteq V$ is \emph{irredundant }if $\operatorname{PN}(v,D)\neq\varnothing$ for each $v\in D$.

> the \emph{upper irredundance number }$\operatorname{IR}(G)$ is the largest cardinality of an irredundant set of $G$.

> an $\operatorname{IR}$-\emph{set} of $G$, sometimes also called an $\operatorname{IR}(G)$-\emph{set}, is an irredundant set of cardinality$~\operatorname{IR}(G)$.

> Following \cite{FHHH11}, we define the \emph{$\operatorname{IR}$-graph }$G(\operatorname{IR})$\emph{ }of \emph{$G$} to be the graph whose vertex set consists of the $\operatorname{IR}(G)$-sets, i.e., the irredundant sets of $G$ of maximum cardinality, where two $\operatorname{IR}(G)$-sets $D$ and $D^{\prime}$ are adjacent if and only if there exist vertices $u\in D$ and $v\in D^{\prime}$ such that $uv\in E(G)$ and $D^{\prime}=(D-\{u\})\cup\{v\}$.

> To prove that a given graph $H$ is an $\operatorname{IR}$-graph, one needs to construct a graph $G$ such that $G(\operatorname{IR})\cong H$.

| Source symbol | Lean definition or theorem |
|---|---|
| N[v] | `ClosedNbr G v w := w = v ∨ G.Adj v w` |
| N[D] | `ClosedNbrSet G D w := ∃ v ∈ D, ClosedNbr G v w` |
| w ∈ PN(v,D) | `IsPrivateNbr`; `privateNbr_closed` proves the closed-neighbourhood difference formula |
| irredundant D | `Irredundant G D := ∀ v ∈ D, ∃ w, IsPrivateNbr G D v w` |
| IR(G) | `IR G`, finite supremum of irredundant cardinalities; `ir_upper`, `ir_attained` |
| IR(G)-set | `IRSet G D := Irredundant G D ∧ D.card = IR G`; `IsIRSet` is an abbreviation |
| D adjacent to D′ | `Swap G D D′`; graph vertices are the subtype of `IRSet` |
| G(IR) | `IRGraph G`, with literal Swap adjacency |
| H is an IR-graph | `IsIRGraph H`, existence of a finite type V, instances, source graph G, and `Nonempty (H ≃g IRGraph G)` |
| explicit witness | `G9`, `ir_G9`, `isIRSet_iff`, `pathIso` |
| negated MathDB claim | `IR350452.conjecture_false : ¬ IR350452.Conjecture` |

No distinctness clause is added to adjacency. The source edge uv already implies u ≠ v because G is simple. `swap_irrefl` proves no loops; `swap_symm` uses equal cardinalities of maximum sets and proves reversal. Symmetry is not imposed by adding a reversed disjunct.

`IsIRGraph` ranges over all finite simple graphs with vertex types in `Type` (universe zero), not only a fixed finite vertex set or the displayed witness. Every finite graph admits a universe-zero representation by a finite index type. Decidable equality and Fintype instances are quantified in the witness; adjacency decidability is not a restriction on the existential graph. The general proofs use classical finite maxima, so every finite simple graph is included. Concrete finite checks use explicit decidable relations.

The conjecture is repeated in Mynhardt–Roux, *Irredundance Trees of Diameter 3*, arXiv:2104.09004v2, Open Problems, Conjecture 1. Both cached primary sources were inspected; no network retrieval was needed in this lane.
