# The helicene minimizes maximal matchings among benzenoid chains

The helicene attains the minimum number of maximal matchings among
benzenoid chains of each length. We count matchings with nine boundary
states and prove five comparisons that allow a constant-turn ending
to be extended toward the beginning of any chain. The comparisons use
finite integer certificates whose cutoffs cover words and runs of
arbitrary length.

## MathDB statement (verbatim)

Let $B_n$ be a benzenoid chain of length $n$, and let $H_n$ denote the helicene benzenoid chain of length $n$. For a graph $G$, write $Psi(G)$ for its number of maximal matchings.

**Extremal maximal-matchings conjecture.** For every benzenoid chain $B_n$ of length $n$,

$$
\Psi(H_n) \leq \Psi(B_n).
$$

The conjecture asserts that the helicene has the smallest number of maximal matchings among all benzenoid chains of the same length. The surrounding discussion presents this as an unresolved extremal problem and notes that maximal matchings appear to decrease as the number of kinky hexagons increases, while their value may also depend on the direction of successive turns.

## Source statement and graph model

Došlić and Short state Conjecture 5.19 as follows. “Let \(B_n\) be a benzenoid
chain of length \(n\). Then \(\Psi(H_n) \leq \Psi(B_n)\).” It is Conjecture 5.1 in
the preprint. [Journal paper, pp. 181–183 and 199](https://doi.org/10.2298/AADM161106003D), [preprint, §2 and §5](https://arxiv.org/abs/1511.00590)

The source defines a matching as a set of graph edges with no common vertex
between distinct edges. A maximal matching is inclusion-maximal among such
sets, and its count is \(\Psi(G)\). The Lean definitions
`IsMatching G M` and `IsMaximalMatching G M` operate on
`Finset (Sym2 V)`. In the second definition, every omitted edge must meet
one of the chosen edges. The equivalence with inclusion-maximality is
`maximal_iff_inclusion`. The function `Ψ G` counts these finite edge sets.

The source's benzenoid system is a connected plane graph without cut vertices
whose bounded faces are hexagons. Two hexagonal faces are “either disjoint
or they share exactly one common edge.” A vertex can be on at most three
hexagons.
A catacondensed system has no vertex on three hexagons. A chain is a
catacondensed system in which no hexagon is adjacent to three others.
Its length is its number of hexagons. An interior hexagon is straight
when its two degree-two vertices are nonadjacent and kinky when they are
adjacent. A polyphenacene has only kinky interior hexagons. Figure 4 depicts
the helicene \(H_n\) as the polyphenacene with all kinks in the same sense.

The graph statement uses `BenzenoidChainWitness G n`. Its data are
an ordered family of injectively indexed six-cycles that cover the vertices
and edges of `G`. Consecutive cycles share precisely the endpoints of
one common cycle edge, nonconsecutive cycles are disjoint, and the two
common edges of any interior cycle are vertex-disjoint.
`helicene n` is the explicit graph that successively glues a new six-cycle
to the offset-two edge, with the endpoints reversed in the next face's
local numbering. `heliceneWitness n` certifies this construction.
The Lean theorem quantifies over every finite graph with this witness.

```lean
theorem MathDB331692 {V : Type*} [Fintype V] (G : SimpleGraph V) (n : ℕ)
    (w : BenzenoidChainWitness G n) : Ψ (helicene n) ≤ Ψ G
```

Mathlib does not provide plane embeddings and faces for this purpose, so
the Lean theorem is a statement about finite graphs with a hexagon-chain
witness, not about plane graphs. Three modelling facts connect it to the
source. They are proved in prose in the next section and are not formalized.

1. Every benzenoid chain of length \(n\) in the source's sense, viewed as an
   abstract graph, has a witness `BenzenoidChainWitness G n`. Only this fact
   is needed to deduce the source's inequality from the Lean theorem.
2. Conversely, every graph with such a witness is isomorphic to a benzenoid
   chain of length \(n\). The Lean class therefore equals the source class up
   to isomorphism, so the Lean theorem is neither weaker nor stronger.
3. `helicene n` is the source's helicene \(H_n\). As a numerical check, its
   maximal-matching counts for \(n=0,\dots,6\) are \(1,5,20,75,288,1094,4171\),
   which are the source's values \(h_0,\dots,h_6\) (Corollary 4.5 of the preprint).

The matching count, the transfer bijection, and the inequality for graphs
with witnesses are proved in Lean.

## From plane chains to ordered six-cycles

Let \(B_n\) be a source chain with \(n\ge 1\). It has at least
six vertices. Connectivity and absence of cut vertices imply
2-connectivity. In a 2-connected plane graph every face boundary is a
simple cycle. An edge occurring twice on a face boundary is a bridge.
If a face boundary visits a vertex twice, two distinct corners of that
face occur at the vertex. Draw a simple closed curve through the vertex
entering the open face through one such corner and returning through the
other. The curve meets the graph only at the vertex. Both regions contain
incident edges, since distinct corners are separated by edges in the
cyclic order in each direction. The Jordan curve theorem then precludes a
path between the two regions after the vertex is deleted, so the vertex is
a cut vertex. Both possibilities contradict 2-connectivity. In particular
the outer cycle bounds a closed disk containing the graph and its bounded
faces.

There is no vertex in the interior of that disk. All the faces at an
interior vertex would be bounded, and each can occur only once in the cyclic
order at that vertex because its boundary is a simple cycle. Catacondensation
then gives degree at most two. Degree less than two is impossible in a
2-connected graph. At degree two the two incident faces would share both
edges through the vertex, forbidden by the common-edge condition.

The graph whose vertices are bounded faces and whose edges are their
adjacencies is connected. Take points in the interiors of two bounded
faces and join them in the open outer disk by a curve avoiding the finitely
many vertices and crossing edges transversely. Its sequence of faces is a
walk through bounded-face adjacencies. Every edge off the outer cycle
separates two distinct bounded faces, since an edge with the same face on
both sides is a bridge. Distinct such edges yield distinct adjacencies,
because any two bounded faces share at most one edge. All vertices lie on
the outer cycle, which has as many edges as vertices. Euler's formula
therefore gives \(|E|-|V|=n-1\) edges off the outer cycle. The face-adjacency
graph is connected, has \(n-1\) edges and maximum degree two, so it is a
path (a singleton for \(n=1\)).

At a vertex on the outer cycle there is one corner of the unbounded face.
If two bounded faces meet there, their two corners are consecutive in the
remaining cyclic order, since catacondensation allows at most two bounded
faces there. The edge separating those corners belongs to both faces.
Thus any common vertex of two bounded faces lies on a common edge. This
also rules out extra common vertices for a pair with exactly one common
edge.

List the bounded faces in path order. Nonconsecutive faces are disjoint.
Consecutive faces have exactly the endpoints of their one common edge
in common. The two shared edges at an interior face are disjoint, since
a common endpoint would belong to three faces. Every graph edge belongs
to a bounded face. An edge incident only to the unbounded face would be a
bridge. Every vertex lies on an edge and hence on a bounded face. Taking
the cyclic vertices of each face supplies every field of
`BenzenoidChainWitness`.

For \(n\ge 2\), orient the face boundaries in the same plane orientation.
They then traverse shared edges in opposite directions. Number the first
face so its outgoing edge is \(23\), and every subsequent face so its incoming
edge is \(01\). Disjointness of the ports puts the outgoing edge of each
interior face at offset \(2\), \(3\) or \(4\), denoted \(L,S,R\) respectively.
When the outgoing edge is \(j,j+1\), the next face's vertices \(0,1\) are
\(j+1,j\) in the previous face's coordinates. Each new face adds four
vertices. At offset three the two vertices away from the ports are
nonadjacent. At offsets two and four they are adjacent, in opposite
positions relative to the oriented ports.

These data determine the abstract graph. Begin with a six-cycle and,
at each step, identify the specified edge of a new six-cycle with the
outgoing edge, with endpoints reversed. Edges and vertices have precisely
these identifications by the witness intersection conditions. Conversely,
the construction has a plane realization by attaching each new polygon
in the unbounded face along the specified outer boundary edge. The new outer
boundary replaces that edge by the other five edges of the polygon and
remains a simple cycle. The graph given by the constant offset-two word
agrees with the source's helicene in Figure 4, up to simultaneous reflection.
Thus a chain of length \(n\ge 2\) has a turn word of length \(n-2\), and its
helicene comparator uses only \(L\)'s. For one face the graph is a six-cycle.
At length zero the empty-chain convention gives the empty graph and one
maximal matching, the empty matching.

## Transfer counts

Use states \((a,b)\in\{0,1,2\}^2\) in lexicographic order on the ordered outgoing pair. A vertex is forgotten when it is no longer in this pair, because no later face can meet it. The partial matching must dominate every edge between forgotten vertices, where domination of an edge means at least one endpoint is matched. A matching is maximal precisely when it dominates all edges. State 1 means the vertex is already matched. State 2 means it is unmatched and must be matched later because it neighbors a forgotten unmatched vertex. State 0 means it is unmatched and has no such obligation.

At each face enumerate all subsets of its six cycle edges for the first face, or the five edges other than \(01\) for all other faces. The edge \(01\) has already been available at the preceding face. Reject any subset which repeats a vertex or uses an incoming vertex in state 1. Let \(Q\) be the matched vertices of the local face, consisting of the endpoints of the chosen edges and the incoming vertices in state 1. Begin an obligation set \(T\) with the incoming vertices in state 2 outside \(Q\). For each cycle edge disjoint from \(Q\), add its second endpoint to \(T\) if its first endpoint is being forgotten, and add its first endpoint to \(T\) if its second endpoint is being forgotten. Reject unless \(T\) is contained in the outgoing pair. Assign outgoing statuses from membership in \(Q,T\), or neither. The last face has no outgoing pair.

The rule preserves the invariant. An old edge to a forgotten vertex can change domination only through an incoming vertex, and an unmatched incoming vertex adjacent to a forgotten unmatched vertex has exactly the recorded obligation. For the current edges disjoint from \(Q\), two forgotten endpoints make the choice illegal. One forgotten endpoint imposes an obligation on the other. If both endpoints remain, the edge is outgoing and will be checked at the next step. All other edges have already been handled. Each final matching determines its choices uniquely since each edge is available at exactly one step. Conversely the choices produce a matching and dominate every edge at the end.

Let \(v\) be the first-face row vector and \(e\) the column vector of last-face counts. Applying the rule gives
\[
 v=(1,1,0,1,3,1,0,1,1),\qquad e=(3,3,2,3,2,2,2,2,1)^{\mathsf T}.
\]
Write \(L,S,R\) also for the three \(9\times 9\) matrices of transition counts from incoming to outgoing states. For a word \(W\) let \(M_W\) be the corresponding product, with the empty product \(I\). Thus \(\Psi(B_n)=vM_W e\). If \(P\) interchanges the coordinates of a state, then \(P^2=I,\ vP=v,\ Pe=e,\ R=PLP,\ S=PSP\). Reflection of the ordered hexagons swaps their ports and reverses the turn, or these identities can be checked from the transition rule.

## Finite certificate for arbitrary prefixes and suffix powers

For an arbitrary prefix \(U\) put \(p=vM_U\). The following inequalities hold over the integers.

| \(D\) | Range of \(h\) | Inequality |
|---|---|---|
| \(L(P-I)\) | \(h\geq2\) | \(pDL^he\geq0\) |
| \(S-RP\) | \(h\geq0\) | \(pDL^he\geq0\) |
| \(L^2R-L^3\) | \(h=0\) | \(pDe\geq0\) |
| \(LRL-L^3\) | \(h=0\) | \(pDe\geq0\) |
| \(SLR-L^3\) | \(h=0\) | \(pDe\geq0\) |

In addition \(v(LR-L^2)e=0\).

For each of the first two rows set prefix cutoff \(k=4\) and power cutoff \(b=7\). Take each word \(A\) of length at most \(k\). When its length is \(k\), test all nine components of \(M_A D L^h e\) for the indicated \(h<b\), and all 81 entries of \(M_A D L^b\). When its length is less than \(k\), test \(vM_A D L^h e\) and all nine entries of \(vM_A D L^b\) instead. For each row with \(h=0\) only, use \(k=3\) and test the corresponding vectors and scalars at \(h=0\). The exact minima are as follows.

| \(D\) | Scalar and vector tests | Matrix and row cutoff tests |
|---|---:|---:|
| \(L(P-I)\) | 11 | 94 |
| \(S-RP\) | 4 | 571 |
| \(L^2R-L^3\) | 11 | |
| \(LRL-L^3\) | 11 | |
| \(SLR-L^3\) | 9 | |

The numbers can be reproduced by listing the subsets of the six edges in the transition rule and then using integer matrix multiplication. The pseudocode below specifies the complete finite calculation using the vectors and matrices defined above. All arithmetic is over the integers. For prefix length at least \(k\), split \(U=BA\) with \(|A|=k\) and multiply the certified componentwise bounds on the left by the nonnegative row \(vM_B\). For \(h\geq b\), multiply the cutoff certificate on the right by the nonnegative column \(L^{h-b}e\). The tests for short prefixes already include the row \(v\). Thus the finite certificate proves the inequalities for all prefix lengths and all indicated powers.


```text
check(D, k, H, b):
    for d = 0, ..., k:
        for A in {L,S,R}^d:
            X = product(A)                 # identity when d = 0
            if d < k: X = v * X
            for h in H:
                assert every entry of X * D * L^h * e is positive
            if b is present:
                assert every entry of X * D * L^b is positive

check(L*(P-I),       4, 2..6, 7)
check(S-R*P,         4, 0..6, 7)
check(L*L*R-L*L*L,   3, {0}, absent)
check(L*R*L-L*L*L,   3, {0}, absent)
check(S*L*R-L*L*L,   3, {0}, absent)
assert v * (L*R-L*L) * e == 0
```

## Minimization

For every word ending in a nonempty run of a single kink letter
(all \(L\) or all \(R\)), we show that
the constant word of the same length has at most its score. Write the word
as \(U T^h\), with \(T\) one of \(L,R\) and \(h\ge 1\). We induct on \(|U|\).
If \(U\) is empty, the assertion follows from reflection invariance.
Otherwise, by reflection, take \(T=L\).

- If the last letter of \(U\) is \(L\), absorb it into the terminal run.
- If the last letter of \(U\) is \(S\), write \(U=AS\). The second
  certificate gives \(vM_A S L^h e\ge vM_A R^{h+1}e\), using
  \(R^h e=P L^h e\). The new prefix \(A\) is shorter.
- If the last letter of \(U\) is \(R\) and \(h\ge2\), use the reflected
  first certificate to replace \(R L^h\) by \(R^{h+1}\). The unreflected
  certificate reads \(vM_A L R^h e\ge vM_A L^{h+1}e\).
- In the remaining case the word ends in \(RL\). The two-letter word
  \(RL\) has the same score as \(LL\) by reflection and
  \(v(LR-L^2)e=0\). If another letter precedes \(RL\), the last three
  letters are \(LRL,RRL,SRL\). The final three certificates, reflected
  for \(RRL\) and \(SRL\), replace those triples by \(LLL,RRR,RRR\)
  respectively. Each leaves a shorter prefix.

Each replacement preserves length and weakly decreases the score.
The induction therefore applies in each case. A word ending with \(S\)
can first replace it by \(R\), using the second certificate at \(h=0\).
The empty word is constant by convention. This proves the constant-turn
minimum for \(n\ge2\). For \(n=1\) the only chain is the six-cycle, with five
maximal matchings. For \(n=0\) the empty graph has the empty matching.
This proves the asserted inequality for all lengths.

The minimizer need not be unique. At \(n=4\) the zigzag chain and the
helicene both have \(288\) maximal matchings, matching \(z_4=h_4\) in the source.
The theorem asserts only that the helicene attains the minimum.

## Lean verification

`orient` reindexes the cycles of any witness by rotations and reversals,
preserving their vertex and edge sets and orienting each common edge as above.
`edgeSlots` assigns each actual edge to its first occurrence and
`matchingChoices` turns edge subsets into families of six local choice bits
with the repeated incoming edge set to zero. The equivalence
`validity_iff_maximal` proves that the transition rule, checked at every face,
characterizes exactly the maximal matchings. Its boundary lemmas express
matched status as incidence to a chosen edge in the processed prefix and
show that a surviving obligation is discharged at the next face. The
equivalence `matchingPaths` identifies these matchings with accepted
choice lists. The recursion `accepted_score` counts the lists by the
matrix product after kernel verification of all local transition counts.

The cutoff check works with columns. At depth zero it checks each entry
of the column for nonnegativity. At a positive depth it checks the pairing
with the initial row and recursively checks the three columns obtained
by prepending a turn to the column product. A second finite check on each
column at power seven permits extension to larger powers by multiplication
with a nonnegative vector. `transfer_minimum` applies the reductions above
and `MathDB331692` transports the minimum to the graph count.

## Significance and prior work

This answers the equal-length extremal question for maximal matchings in
a benzenoid chain. A transfer formula for a prescribed chain gives its
count but leaves the comparison across different sequences of turns open.
The five terminal comparisons establish that a constant-turn chain attains
the minimum. Their proof uses finite certificates that control both arbitrary
prefixes and arbitrary lengths of the last run.

The bounded prior-art review found no earlier proof. Došlić and Short establish the maximum at the
polyacene in Theorem 4.6 of the preprint. Conjecture 5.19 of the journal
version asks for the minimum. Shi and Deng give a transfer count for
an arbitrary benzenoid chain. Chen and Zhang cite that count in Remark 4.1
and still pose the minimum for lengths at least four as Conjecture 5.2 in
2025. The review also checked
the arXiv history, citation records, and accessible proof registries. These
checks found no resolution of this minimum. [Došlić–Short (2021)](https://doi.org/10.2298/AADM161106003D), [Shi–Deng (2023)](https://doi.org/10.1016/j.amc.2023.127922), [Chen–Zhang (2025)](https://www.pmf.ni.ac.rs/filomat-content/2025/39-33/39-33-24-28109.pdf)
