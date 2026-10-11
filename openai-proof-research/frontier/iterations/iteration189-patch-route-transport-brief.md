# I189: patch-route classification and survivor transport

Work only in `/home/mj-kang/Documents/Dev/math/openai-proof-research`.
Read AGENTS.md and `sources/upstream.json`; all OpenAI results at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true.
Eight accepted, two remaining. Neither bookkeeping nor technical
progress automatically supplies a substantial finding.

## Focused context and unchanged target

Read all five I188 outputs and the
[finalized parent disposition](i188-patch-rooted-state-parent-disposition.md).
Read the I188 brief and the actual source operations it used. The
original E183 hypotheses are exactly I188 analytic Section 0, unchanged:
arbitrary finite connected simple bipartite locally cubic disk $X$,
five degree-two ports in order $(0,2,1,4,3)$ with colors
$(1,1,1,0,1)$; exact thirteen-vertex exterior $Y$ and attachments at
$(1,5,6,28,29)$; simple planar bipartite brace $G$; all eleven complete
nonempty survivor fibres and complete lost $P=(01;01)$, $D=(0134;01,34)$;
internal port-disjoint $C=(x,a,b,y,d,c,x)$ with chord $xy$,
$A=\{xa,by,dc\}$ and $B=\{ab,yd,cx\}$; $p\in P$ using exactly $A$ and
$q=p\triangle E(C)\in P$. For every such instance E183 asks for **some
perfect matching containing $A$ whose complement is Hamiltonian of any
survivor local type**. Restate the exact exterior, complete fibres and
quantifiers in your argument, not just this shorthand. No cut-2,
fixed-completion, single-difference-cycle, or local-move prescription.
The local-ear mechanism remains PARKED; do not revive it as a plateau
or transfer task, and do not use any sequence of iterated improvements.

I188's original deductions pass parent review without repairs. Now paid
and reusable at their stated scopes:

* Both squares $(x,a,b,y,x)$ and $(x,y,d,c,x)$ are facial; the six dual
  triangles $t_x=(o,\ell,r)$, $t_a=(\ell,o,u)$, $t_b=(\ell,u,v)$,
  $t_y=(\ell,r,v)$, $t_d=(r,v,w)$, $t_c=(r,o,w)$ are distinct, tile a
  disk with boundary $(o,u,v,w)$ dual to
  $\partial V(C)=\{aa',bb',cc',dd'\}$, and have roots $\{o,\ell,r\}$.
* The endpoint mark $\eta$ forces one consistently signed marked cycle
  per source group; the marked sum is nonzero; every marked partnered
  forest state recovers a perfect matching containing $A$ with
  Hamiltonian complement. The $A$-containing fixed-root source image is
  nonempty. (You need not reuse the state-sum machinery; these facts are
  available if useful.)
* Every $A$-containing matching's complement has exactly the patch
  routes $a'\!-\!a\!-\!b\!-\!b'$ and $c'\!-\!c\!-\!x\!-\!y\!-\!d\!-\!d'$,
  using $B\cup\{xy\}$ and all four continuations; conversely any
  Hamiltonian cycle with those routes has complementary matching
  containing $A$. The hexagon toggle $A\leftrightarrow B$ preserves the
  continuation pairing and the full local type.
* Exact exterior classification without cut 2 (parent-verified by
  exhaustive enumeration of the declared $Y$): used sets
  $01,04,14,0134$ only, with $04$ impossible; compatible exteriors are
  exactly three paths $R_1,R_2,R_3$ for $01;01$, one path $S$ for
  $14;14$, three packings for $0134;03,14$, and one packing for
  $0134;01,34$. Hence a Hamiltonian cycle $H$ survives iff
  $2\in U(H)$ or its type is $14;14$ or $0134;03,14$.
* From I183: removing $A$ bijects $A$-containing perfect matchings with
  perfect matchings of $G'=G-V(C)$; the four continuation terminals
  $a',b',c',d'$ are distinct vertices outside $C$.

## The survivor-transport route to investigate

The survivor fibres are nonempty but their members need not use the
canonical patch routes. E183 is equivalent to: **some survivor-typed
Hamiltonian cycle uses the canonical patch routes**. Investigate whether
transport to canonical routes is always possible.

1. **Classify all patch restrictions symbolically.** A Hamiltonian cycle
   restricts to the eleven local edges ($E(C)$, chord $xy$,
   continuations $aa',bb',cc',dd'$) with degree exactly two at each of
   $x,a,b,y,d,c$. Enumerate all such local patterns in a written
   symbolic classification (no research code): group by the set of used
   continuations and the induced pairing/paths on the terminals
   $\{a',b',c',d'\}$ and on $\{x,a,b,y,d,c\}$. Prove completeness.
   Record which patterns are the canonical $A$-routes, the toggled
   $B$-routes, the two-continuation patterns (such as
   $a'\!-\!a\!-\!b\!-\!y\!-\!x\!-\!c\!-\!d\!-\!d'$), and any others.

2. **Admissibility constraints.** For each pattern, determine what the
   rest of $X$ must supply (a pairing on the used terminals, absence of
   closed sub-cycles) for the global cycle to be single and
   Hamiltonian, and what planarity/bipartiteness/brace hypotheses exclude
   outright. The five-port type depends on the used-continuation set and
   on how the induced paths thread to the ports; state exactly how.

3. **Transport or obstruction.** Given an arbitrary survivor-typed
   Hamiltonian cycle (one exists in each of the eleven fibres) whose
   patch restriction is non-canonical, determine whether there exists a
   modification of the patch restriction — with a compensating change of
   the matching, and where necessary an explicit rerouting of the
   affected exterior-to-patch connections — that yields a Hamiltonian
   cycle using the canonical routes while preserving a survivor local
   type. Handle the pairing dichotomy explicitly: if the rest-induced
   pairing on $\{a',b',c',d'\}$ equals the canonical patch pairing
   $(a'b')(c'd')$, the canonical routes close two cycles, so identify
   what else must change. Type preservation must be proved from the
   paid exterior classification, not asserted from local pictures.

4. **Three-way verdict.** Deliver exactly one of:
   * **Transport PROVED**: every admissible instance has a
     survivor-typed Hamiltonian cycle with canonical routes, hence E183
     PROVED (state the implication chain completely);
   * **E183 REFUTED**: a fully hypothesized admissible instance (all
     E183 hypotheses verified, including complete fibres and the
     $p,q$ condition) in which every canonical-route Hamiltonian cycle
     has lost type, with all computations written out;
   * **UNRESOLVED**: the precise class-by-class obstruction, with every
     settled class proved and the open classes identified exactly.
   Do not declare partial transport a proof. Do not nominate a
   substantial finding; the parent decides acceptance.

5. **Separation from the source route.** I188 left unpaid the
   implication (18) that its marked source image contains a survivor.
   This brief does not ask you to pay (18); the transport route attacks
   the full population (17) directly. If your analysis shows transport
   interacts with the fixed-root source image (e.g., a recovered
   survivor's canonical state), record it as a remark, not a claim.

## Sources, evidence and exclusive output scope

Use the retained pinned manuscript at
`frontier/sources/i164_structural_graph_discovery/upstream-paper.tex`,
SHA-256 `03f59643501a21f2b20c138ff10769fde41523008845b2528bf646b4a769dd56`.
Read actual needed statements/operations and record ranges; check the
focused catalogue/companion paths. No recursive history or upstream
truth audit. No external theorem may be invoked unread.

Only these five paths may be written:

- `frontier/iterations/i189-patch-route-transport.md`
- `frontier/experiments/i189_patch_route_transport/analytic-attempt.md`
- `frontier/experiments/i189_patch_route_transport/reading-and-failures.md`
- `frontier/experiments/i189_patch_route_transport/input-authentication.json`
- `frontier/sources/i189_patch_route_transport/literature.md`

No research code, graph/state/matching scans or tests, experiments,
historical replay/control rebuild, source copies, snapshots or seals.
Written symbolic classification and case analysis about actual
hypothetical admissible instances are allowed and expected. No further
agents, ancestor/shared-ledger edits, staging, commits or publication.
Preserve failed written routes and reading limits. Write the five files
early with explicit partial status and update them incrementally as
sections stabilize, so an interruption leaves verified partial state.

Before proof work authenticate all ten I187/I188 anchors:

| Output | SHA-256 |
| --- | --- |
| I187 report | `6c37f8f35bbbefd181473335a7d1013532d92be70afa17c9717d4508b5d10734` |
| I187 analytic attempt | `9ba0316f9db9d344b39b3d5637e4474d790696bcd2cdea7016698a611f98468f` |
| I187 reading/failures | `a62333f9e1cd118ddd9a751b55906fc1303ff02bc361e75b49d3b48cdd9afa6e` |
| I187 authentication | `8d398bd1811d0bc5939fe7b5899888213138a3a9cb2b5b66202178db91ddefe5` |
| I187 literature | `686e3c5e5334c4ec0d267488ee7142c1a2ba7b9618da81c20d334a0c72d80947` |
| I188 report | `3489a0d5a98d7f48f34e05853eb875651d7d7b9b2e96a05667a0beedbbab8e29` |
| I188 analytic attempt | `d1fc472d25e74f345bb0ed79d7df1aa8074ef0f0278f5f5f826f69816707de5c` |
| I188 reading/failures | `f7bca5bf8df8eaa93a13c09ea34593fadcc724e1ee108848a8c65cdc3228f3ff` |
| I188 authentication | `4825a58ef9794675587b8a9012452f550409a2de750304b408091fb174669a47` |
| I188 literature | `937b693acbde539b774ad203981065d46d3ad4abfb1efce7120fdbb4af5ef8c9` |

Also hash this brief, both finalized dispositions and actual additional
inputs. The parent independently checked I188's proofs and re-derived
its exterior table by exhaustive enumeration; the inherited 23-stage
replay passed in about 8.71 seconds. It and the twelve facial/626
matching controls remain finite and must not be rerun here.
Return detached hashes, full written deductions or gaps, the
original-target verdict and source/contribution limits. This is an
unsealed proof record.
