# I190: beta-paired cycle-free complements and survivor type

Work only in `/home/mj-kang/Documents/Dev/math/openai-proof-research`.
Read AGENTS.md and `sources/upstream.json`; all OpenAI results at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true.
Eight accepted, two remaining. Neither bookkeeping nor technical
progress automatically supplies a substantial finding.

## Focused context and unchanged target

Read all five I189 outputs and the
[finalized parent disposition](i189-patch-route-transport-parent-disposition.md).
Read the I189 brief and the actual source operations it used. The
original E183 hypotheses are exactly I189 analytic Section 0, unchanged
(arbitrary admissible $X$; exact thirteen-vertex $Y$; simple planar
bipartite brace $G$; eleven complete nonempty survivor fibres; complete
lost $P=(01;01)$, $D=(0134;01,34)$; internal port-disjoint $C$ with
chord $xy$; $A=\{xa,by,dc\}$; $p\in P$ with $E(p)\cap E(C)=A$ and
$q=p\triangle E(C)\in P$; $R=G-V(C)$; terminals $a',b',c',d'$ distinct
and outside $C$). Restate the exact exterior, complete fibres and
quantifiers in your argument. For every such instance E183 asks for
SOME perfect matching containing $A$ whose complement is Hamiltonian of
ANY survivor local type. No cut-2, fixed-completion,
single-difference-cycle, or local-move prescription. The local-ear
mechanism remains PARKED; no iterated improvement sequence.

I189's original deductions pass parent review without repairs; the
classification was independently re-derived by exhaustive enumeration.
Now paid and reusable at their stated scopes:

* Exactly seven Hamiltonian patch restrictions are possible:
  canonical $K_A$, toggled $K_B$, four-continuation $F$ (rest pairing
  $\alpha=(a'b')(c'd')$), and two-continuation paths
  $L_{ab},L_{cd},L_{bc},L_{ad}$. The rest pairing $\gamma$ is excluded
  by planarity; $K_A,K_B$ require rest pairing $\beta=(a'c')(b'd')$.
* $K_B$ transports to $K_A$ by the hexagon replacement, preserving the
  full local type. $F$ with a balanced $(2,2)$ cut distribution and
  used set containing port 2 transports to a canonical survivor by the
  eight verified exterior witnesses, interchanging the two local
  pairings. The same repair at $U=0134$ converts survivor $03,14$ to
  lost $D$. An unbalanced cut distribution leaves a closed $X$
  component immune to exterior-only repair.
* Two-continuation rows admit a perfect-matching repair of the two
  unused terminals by one alternating path against the known $q$
  completion; adjacency of the unused terminals (or the $\beta$
  traversal order in the mixed rows) gives full-type-preserving
  canonical transport. General repairs are uncontrolled.
* The exact necessary-and-sufficient condition (T_R): E183 holds on an
  admissible instance iff SOME perfect matching $N$ of $R$ has
  $E(R)\setminus N$ cycle-free with terminal pairing $\beta$, AND the
  traced canonical candidate has survivor type by the paid criterion
  (S) ($2\in U$, or $14;14$, or $0134;03,14$). The known $q$ witness
  satisfies the first condition with lost type $P$.
* From I188: the $A$-containing fixed-root source image is nonempty;
  every canonical-route Hamiltonian cycle corresponds to a matching
  containing $A$; the complete no-cut-2 exterior table.

## The beta-pairing route to investigate

Both geometric routes now terminate at (T_R). Investigate the pairing
layer itself.

1. **Brace consequences for $R$.** Read the manuscript's actual brace
   statements and its two-edge extension consequences (the dual-strategy
   and pair-existence ranges, and any brace lemmas actually used). Derive
   what braceness of $G$ forces about perfect matchings of $R$ near the
   four terminals: which edges at $a',b',c',d'$ can be simultaneously
   matched or avoided, and what connectivity the complement
   $E(R)\setminus N$ must have. Prove each consequence from the read
   statements; do not import external matching-structure theorems
   unread.

2. **The $\beta$ versus $\alpha$ dichotomy.** For a perfect matching
   $N$ of $R$ whose complement has two terminal paths (no cycle
   component), the pairing is $\alpha$ or $\beta$ by the paid planarity
   argument. Determine what distinguishes the two cases in matching
   terms (e.g., parity, alternating-path structure between matched
   pairs, or the manuscript's circulation/Pfaffian sign operations in
   lem:circulation and cor:pfaffian-paths, lines 485–561 and 794–828,
   which I189 read but did not use). A proved criterion converting an
   $\alpha$ witness to a $\beta$ witness by a controlled matching change
   would be decisive; state exactly what it does and does not pay.

3. **Concentration exclusion.** Equivalently, assume an admissible
   instance in which EVERY survivor-typed Hamiltonian cycle lies in an
   open I189 class (no $K_A/K_B$ survivor, no balanced cut-2 $F$
   survivor, no short-repair $L$ survivor) and every canonical
   candidate is lost. Derive a contradiction from the brace hypothesis
   and the complete eleven survivor fibres, or show the assumption is
   consistent and identify the exact extra structure a counterexample
   needs. Cycle-free cycle-count or parity arguments are allowed if
   fully written.

4. **Survivor type control.** Any successful $\beta$ complement must
   also satisfy (S). Use the paid exterior table: for $U$ containing 2
   the explicit witnesses supply both pairings; for $U=14$ the packing
   $S$; for $U=0134$ only pairing $03,14$ survives. State the
   type-tracing of your candidate completely.

5. **Three-way verdict.** Deliver exactly one of:
   * **E183 PROVED**: a complete implication chain from the E183
     hypotheses to a survivor-typed canonical Hamiltonian cycle;
   * **E183 REFUTED**: a fully hypothesized admissible instance (all
     hypotheses verified, including complete fibres and $p,q$) with no
     canonical survivor, all computations written out;
   * **UNRESOLVED**: the precise remaining assertion, with every settled
     subcase proved. Partial pairing results are not a proof.
   Do not nominate a substantial finding; the parent decides acceptance.

## Sources, evidence and exclusive output scope

Use the retained pinned manuscript at
`frontier/sources/i164_structural_graph_discovery/upstream-paper.tex`,
SHA-256 `03f59643501a21f2b20c138ff10769fde41523008845b2528bf646b4a769dd56`.
Read actual needed statements/operations and record ranges; check the
focused catalogue/companion paths. No recursive history or upstream
truth audit. No external theorem may be invoked unread.

Only these five paths may be written:

- `frontier/iterations/i190-beta-pairing-survivor.md`
- `frontier/experiments/i190_beta_pairing_survivor/analytic-attempt.md`
- `frontier/experiments/i190_beta_pairing_survivor/reading-and-failures.md`
- `frontier/experiments/i190_beta_pairing_survivor/input-authentication.json`
- `frontier/sources/i190_beta_pairing_survivor/literature.md`

No research code, graph/state/matching scans or tests, experiments,
historical replay/control rebuild, source copies, snapshots or seals.
Written symbolic case analysis about actual hypothetical admissible
instances is allowed and expected. No further agents,
ancestor/shared-ledger edits, staging, commits or publication. Preserve
failed written routes and reading limits. Write the five files early
with explicit partial status and update them incrementally as sections
stabilize, so an interruption leaves verified partial state.

Before proof work authenticate all sixteen anchors:

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
| I189 report | `aa2f6bf9895a13616e50ed4e00e58ab67cbb1c419305ac47a3f8980f288aa3bc` |
| I189 analytic attempt | `933cc7de3160960a707042bceae32d4994540dfea008b2a52b1e4f73a8e1eee0` |
| I189 reading/failures | `a5e2270acce653fd48ca27e1768e3a8656a9c023c1d5174071383ccdcbdb1eb5` |
| I189 authentication | `af8f841f730e6913ea34ac5a9d41c68424353b94ab360690a15abe6e5f88c1d6` |
| I189 literature | `d4977bb0d1b1e5ad7200587a3341fb6b3d7b6047766fcaa7bfb64e6b734e583f` |
| manuscript | `03f59643501a21f2b20c138ff10769fde41523008845b2528bf646b4a769dd56` |

Also hash this brief, the three finalized dispositions and actual
additional inputs. The parent independently checked I189's
classification by exhaustive enumeration and its exterior witnesses
edge-by-edge; the inherited 23-stage replay passed in about 8.79
seconds. It and the twelve facial/626 matching controls remain finite
and must not be rerun here. Return detached hashes, full written
deductions or gaps, the original-target verdict and
source/contribution limits. This is an unsealed proof record.
