# MathDB 381600 — rooted transfer investigation, HOLD

**No discovery, counterexample, submission recommendation, or formalization. Credit 0.** The supported interpretation of the intended invariant is a multiset of individual ranks, separated by bidegree and black-set size. The rooted transfer mechanism below is valid, but no nonisomorphic equivalent gadgets were found in the bounded class tested. Neither the conjecture nor its negation has been proved.

## Source scope and resolution of the aggregation issue

Target: Daniele Celoria, *Filtered simplicial homology, graph dissimilarity and überhomology*, [arXiv:2105.03987v2](https://arxiv.org/abs/2105.03987v2), accepted version, 1 December 2022; Section 5, Equation (8), Definition 5.2, Conjectures 5.1/5.4, Definition 5.5. The quantifiers concern **all finite simple connected graphs**, up to isomorphism, with a fixed common number of vertices. A solution needs equality of every level of the invariant for a connected nonisomorphic pair, or a proof that no such pair exists. Work with graphs as one-dimensional simplicial complexes, not their clique complexes.

The live arXiv page still identifies v2 as current. A fresh request to the versioned PDF gives SHA256 `5a69012cdc6122fafb561c8985398885a72558d9e3ce18275354c020417a87e7`, exactly matching `../discrete/sources/celoria.pdf`. It is reused by reference. Section 5 was read in full, including the worked example, detection lemmas and computational claims. The v1 TeX was fetched directly and its same grouping language inspected (`v1-uberhomology.tex`, original source archive and receipt retained). The [journal page](https://link.springer.com/article/10.1007/s10801-022-01205-3) dates publication to 25 January 2023, pp. 859–904; its full text requires subscription, so no claim that the published body has been independently verified.

Definition 5.2 specifies sorted individual tuples after forgetting the colouring label, but its grouping sentence and Example 5.3 can be read as summation. The decisive additional primary evidence is the [author's dissimilarity code](https://github.com/dceloriamaths/Graph-Uberhomology/blob/64dd49d40efd18c522acdb2caa6f0690180a92ad/dissimilarity_graphs.txt), public repository current HEAD `64dd49d40efd18c522acdb2caa6f0690180a92ad` (14 November 2021). The old account URL redirects to this repository. Lines 148–163 append each colouring's rank tuples, concatenate the lists, sort them, and compare the lists. They do **not** sum ranks or deduplicate repeated tuples. This directly supports the marginal-histogram interpretation; the degree-sequence detection statement and reported tree computations also support it. This is source interpretation, not a certification that every part of that Sage implementation is correct. In particular its zero-rank handling and boundary cases should not be imported as mathematical definitions.

Accordingly the search retains the **stronger joint histogram** of all five ranks for each black-set size, which implies equality of the intended marginal histograms and also of their sums. Zeros can be dropped afterward without changing that implication. The example's printed totals are not used to redefine the problem. The sibling same-degree tree/summed-rank observation remains only a definition-consistency control; it is not repackaged as a result here.

## Ordinary reduction and complete conditional transfer argument

For a graph with n vertices and m edges, a black set S has statistics

- k = |S|, e = number of edges within S, c = number of components of the induced black graph (c = 0 for S empty);
- q = number of mixed-colour edges, z = number of white vertices with no black neighbour.

In the bidegree order (0,0), (1,0), (0,1), (1,1), (1,2), the horizontal homology ranks over F₂ are

`(c, e-k+c, z, q-(n-k)+z, m-e-q)`.

Ordinary proof: the filtration-zero boundary is the incidence matrix of the induced black graph, of rank k-c. A spanning forest gives k-c independent columns, and every other edge column lies in their span. In filtration one, the mixed edges ending at each fixed white vertex all have that vertex as boundary. Distinct white vertices give independent rows, so this boundary has rank n-k-z. Filtration two has only white-white edges and zero horizontal boundary. There are no two-simplices. Subtract the boundary ranks from the corresponding chain dimensions. This agrees with Equation (8) and the paragraph describing filtration zero. Thus equality of the histogram of (k,e,c,q,z), with n,m fixed, suffices for equality of all five-rank joint histograms.

For a rooted graph (A,r), define b = 1 if r is black, otherwise 0. When b=0, define d = 1 if r has a black neighbour inside A; when b=1, set d=0. Let z* count the undominated white vertices **other than r**. Define its transfer signature to be the multiset of

`(k,e,c,q,z*,b,d)`

over **all** black subsets of A. Equivalently use the four state-indexed generating polynomials, with coefficients counting subsets, in variables marking k,e,c,q,z* (the black d=1 state is empty). A valid substitutable pair must also have equal vertex and edge counts. This is a sufficient signature, not claimed to be minimal.

**Conditional transfer lemma.** If two rooted graphs A,A' have equal n,m and equal transfer signatures, identifying their roots with the root of any fixed rooted graph B gives equal full joint rank histograms.

Proof in full: use disjoint vertex sets except for the identified roots and add no other edges. Every black subset of the glued graph corresponds uniquely to a pair of black subsets of A and B whose root colours agree. For a compatible pair with common b, the statistics of the union are

```
n = nA+nB-1,       m = mA+mB,
k = kA+kB-b,       e = eA+eB,
c = cA+cB-b,       q = qA+qB,
z = z*A+z*B + (1-b)(1-dA)(1-dB).
```

The component formula holds because, precisely when the common root is black, its two black components merge into one; all other components remain disjoint. Interior vertices gain no neighbours from the other graph, so their domination status does not change. A white root is undominated exactly when it has no black neighbour on either side, which gives the last term. The other counts follow by disjointness of edges and the single shared vertex. Therefore the number of subsets giving each output tuple is the sum of the products of the input multiplicities over compatible input tuples. Replacing A by A' preserves each product-sum. Applying the rank formula proves the claim at every black-set size and every bidegree. If A,A',B are connected the glued graphs are connected and simple. **Nonisomorphism of the glued graphs remains an independent obligation**; nonisomorphism of rooted gadgets alone does not automatically prove it.

This lemma is a search tool and elementary counting bridge, not a solution of the source conjecture. Its unpaid premise is an actual pair of rooted nonisomorphic gadgets with equal transfer signatures, followed by a host for which the resulting unrooted graphs are nonisomorphic.

## Exact bounded diagnostics

`search-input.json` contains the actual finite input, generated using NetworkX 3.6: one representative of every unlabelled tree through 13 vertices, with one root per rooted-isomorphism class, plus every root of each connected non-tree graph from its graph atlas through 7 vertices. The 2,288 tree graphs yield 20,299 rooted tree classes; 971 atlas non-trees yield 6,639 additional rooted inputs. The per-order tree counts are in `search-scope.json`. The atlas roots include automorphic repetitions.

`rooted_search.js` examines **all 2^n subsets for every input**, retaining the joint rooted tuple, including component count, edge count, mixed-edge count and undominated-white count. Each tuple is encoded injectively in base 64; every coordinate in this input is below 64, and the seven-coordinate integer is below 2^42, hence exactly represented by JavaScript numbers. Sorted arrays retain multiplicity. Two 32-bit hashes only select candidate buckets: **every reported match is re-evaluated and compared entry by entry**. Thus a hash collision cannot certify false equality or suppress a true equal signature.

Result: 3,259 graphs, 26,938 rooted inputs, 2,538 exact equal-signature pairs, all within the same underlying atlas graph. A separate Python exhaustive adjacency-preserving bijection check fixing the root found all 2,538 pairs rooted-isomorphic. **No usable gadget collision.** The successful run took about 8.15 seconds, under a 150-second between-graph wall cap and a 768 MiB Node old-space limit. These are implementation resource bounds, not an assertion that total process address space was capped. The obsolete attempted C++ implementation was removed after the compiler was unavailable.

Independent validation in `validate_transfer.py` uses set-based component traversal and tuple Counters. It matched the actual JavaScript signatures on 18 probes / 16,974 subsets, and checked the coalescence formula against direct enumeration on 100 seeded rooted graph pairs / 33,360 glued subsets, with no failures. Validation had a 90 CPU-second / 700 MiB address-space cap. These checks support the implementation; the proof of the transfer lemma is the ordinary argument above.

Reproduce the search from the preserved input with `node --max-old-space-size=768 rooted_search.js`, then `python filter_equalities.py`. The independent validation uses preserved `signature-probes.json`. Regenerating input with `prepare_search.py` additionally requires NetworkX 3.6; the downloaded dependency directory was removed. No random regular search or Whitney-flip experiment was repeated. Sibling diagnostics are referenced and hashed in `inherited-references.json`, without copying historical evidence trees.

## Exclusions, public registry and prior-art bounds

The campaign ledger, prior-campaign context, later 52-acceptance ledger, fresh status file and sibling screen were parsed. MathDB 381600 is not among their accepted targets; the explicit 369163 exclusion is preserved. No accepted/in-review target was pursued. See `exclusion-receipts.json`; this relies on repository-visible campaign records and the user's assignment, not inaccessible threads.

Current heads fetched during this investigation:

- OpenAI/math `4eaee87548250b2682affda7d05d947c05554bae`, dated 30 October 2026;
- the-omega-institute/trureturing `5a97247bf6ad10485d8891db5430b9e34def4933`, dated 6 November 2026 UTC (5 November locally).

The actual nonrecursive roots were retrieved. OpenAI's entire `preprints` subtree was untruncated; `lean` and `lean/OAI` were truncated recursively and were therefore split by their immediate subtrees until every leaf retrieval was untruncated. The merged listing contains 174,506 files across preprints and Lean. Omega `Problems`, `Library`, `Reg`, `Evidence` were each untruncated, containing 7,598 files together. The exact subtree SHAs, responses, completeness flags and retrieval receipts are preserved; no claim relies on a truncated root-tree grep. Other administrative or trace subtrees were not treated as mathematical registries.

Full path screening found no Celoria/dissimilarity/überhomology/381600/2105.03987/horizontal-homology target match. A bounded body screen retrieved 177 pinned text files: the full Omega GraphInvariants library, selected related problem statements, relevant OpenAI preprint READMEs and current catalogues. All were HTTP 200 and had no target-name/ID/phrase hits. This is **not** a mathematical subsumption review of all registry bodies. Bounded live web queries also surfaced no resolution; exact queries and scope are in `prior-art-search.json`. The related connected-domination paper surfaced by citation and is not claimed cleared for subsumption. The live MathDB receipt still has no posted solution, which is not novelty evidence. Since no candidate theorem survives, neither priority clearance nor publication chronology sufficient for acceptance is claimed.

## Precise hold, next mechanism, Lean feasibility

**Unpaid mathematical gap:** no connected nonisomorphic pair with equal full joint histogram, and no reconstruction proof. The single-root transfer identity is established, but its needed nonisomorphic equal-signature gadgets were not found. This bounded class does not exhaust rooted graphs, and the signature is stronger than the source marginals, so its failure does not support the conjecture.

A concrete next mechanism would be a **two-terminal** transfer: retain terminal colours, the connectivity partition of the black terminals, both terminal domination bits, and the internal (k,e,c,q,z*) counts. Equal tensors, or a proved terminal-swap identity under a carefully chosen host, would allow cancellation in gluing that need not arise from equal single-root signatures. Its component-merging correction must be proved from the terminal connectivity partition, and white-terminal domination must use the OR of internal and external black-neighbour bits. No such tensor identity or candidate pair is available here; this is a new possible search direction, not a surviving tractable construction warranting further investment now. Park the target unless a concrete identity is found.

A modest explicit collision would be feasible to formalize: define finite simple graphs and black subsets; prove the two incidence-rank formulas and the bridge from the combinatorial histogram to the source's positive-rank tuple multiset; kernel-check all subset multiplicities; certify connectedness; prove nonisomorphism using a structural invariant or a complete permutation argument. Transfer-based large constructions would additionally need the coalescence/tensor convolution theorem. No Lean code, literal proved Lean endpoint, or claim of residual-bridge-free formalization is supplied. Root must obtain independent review before deciding whether any future construction merits formalization.

All writes stayed in this assigned directory. No child agents, shared edits, git operations, external messages, account mutations or public posting.
