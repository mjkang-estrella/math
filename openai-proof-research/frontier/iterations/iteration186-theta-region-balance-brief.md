# I186: full-theta region balance, a final bounded local-ear attempt

Work in `/home/mj-kang/Documents/Dev/math/openai-proof-research`.
Read AGENTS.md and the pinned source contract and relevant family-180
catalogue/manuscript entries. All OpenAI results at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true.
Eight accepted, two remaining. No lowered contribution gate.

## Focused inputs and unchanged universal target

Read the complete I185 brief and all five I185 outputs, the
[I184 target brief](iteration184-alternating-cycle-brief.md), and the
[new parent disposition](i185-connected-reconnection-parent-disposition.md).
Read earlier mathematical definitions or actual source statements only
as needed. No recursive audit of unrelated history.

Retain EVERY exact H180/I181 hypothesis in those briefs: arbitrary
locally cubic bipartite disk $X$ with five specified ports, order and
colors; the exact thirteen-vertex $Y$ and its fixed cut attachment;
simple planar bipartite brace $G$; all eleven complete nonempty
survivor fibres and complete lost $P$; internal port-disjoint patch
$C=(x,a,b,y,d,c,x)$, chord $xy$, halves $A=\{xa,by,dc\}$ and
$B=\{ab,yd,cx\}$; $p\in P$ using exactly $A$ and
$q=p\triangle E(C)\in P$.

Z184 still asks for **some** completion $H_0$ of each such $q$ and
a simple $M_0$-alternating cycle $Z\subseteq G'=G-V(C)$ through
$e_2$, with connected $H_0\triangle E(Z)$. Here
$M_0=E(G)\setminus E(H_0)$. Z184 implies E183, but the converse
and strict separation remain unproved. Do not silently replace
the existential completion quantifier.

I184 pays existence of an alternating cycle through every edge of
every residual perfect matching. I185 and its parent review pay the
ear endpoint/arc restrictions and $c'=c-a+b$, not the existence of
an improving ear.

## Original mechanism and exact known formulas

Minimize $(c(H_0,Z),|Z|)$ globally over all completions and qualifying
cycles. For an actual proper alternating ear $Q$ of $Z$:

- $Q$ has nonmatching endpoint edges, odd length, opposite-color
  endpoints and internal vertices outside $Z$.
- Only the arc $I$ with nonmatching endpoint edges can be removed.
  The retained arc $J$ has matching endpoint edges and must contain
  $e_2$.
- $I,J,Q$ form an embedded theta. With $F=H_0\triangle E(Z)$,
  $L=T_I\cup R_Q$, $N=R_I\cup T_Q$, and retained-path pairing $S$
  of $F-L$, the new component count is
  $c'=c-a+b$, where $a=\#\operatorname{comp}(S\cup L)$ and
  $b=\#\operatorname{comp}(S\cup N)$.

All edge identities, loops, parallel edges and common-refinement
singleton paths must be retained. An ear joining different old
components need not improve these abstract pairings. Ordinary
matching reachability does not supply a component-reducing ear.

The formal zero-gain pattern is

$$
L=\{12,34,56\},\quad N=\{23,45,61\},\quad S=\{12,36,45\},
\quad Q=(1,2,3,4),\quad I=(1,6,5,4).
$$

It has $a=b=2$, different endpoint components, and $|I|=|Q|=3$.
It is bipartite and locally noncrossing on the difference boundary.
It does NOT supply $J$, a simultaneous Hamiltonian $H_0$ or any
full exact-instance realization.

## One specific new structural question

Analyze the THREE regions of the full embedded theta $I\cup J\cup Q$
in the original cubic graph $G$, not merely a drawing of $S$ on
one side of $I\cup Q$.

Every theta vertex is already incident with its unique $M_0$ edge
on the theta. Investigate and prove precisely the resulting matching
closure of each region's interior: can any interior vertex be matched
across the theta boundary? Derive the corresponding black/white
boundary-stub balance by counting degrees and matching pairs, retaining
all boundary-to-boundary chords and components.

This is a candidate structural constraint to be checked, not permission
to assume a stronger region or ear theorem. Work in $G$ so cubic degree
counting is legitimate. The patch $C$ lies in a theta region because the
theta avoids it; account for its matching edges $A$ and continuations.
If instead counting in $G'$, explicitly include the four terminal
deficits. Distinguish matching edges from the two complementary
Hamiltonian edges at every boundary vertex.

Then use the actual region balances and $H_0$'s single-cycle condition
to determine whether the I185 zero-gain pattern can be completed by
a retained matching-ended arc $J$ in the full theta picture, and whether
the constraints force an eligible improving ear when $c>1$.

The desired progress is a concrete additional theorem, exclusion, or
precise obstruction that uses this full geometry. Do not simply repeat
the formula $b<a$, claim that every noncrossing pattern is realizable,
or assume exclusion of one six-label pattern proves universal progress.
Conversely, a compatible local full-theta pattern alone would still not
be a graph counterexample with the exact exterior, brace and fibres.

No new graph construction, generation, tests, attachment changes,
parameter sweeps, matching scans or research code. Reason symbolically
about actual hypothetical admissible instances and their regions.

## Stopping rule

This is the last bounded pass on the single-ear local-improvement
mechanism unless the region analysis supplies a genuinely new bridge.
If it yields only necessary bookkeeping conditions without a usable
improvement or structural exclusion, explicitly recommend **parking
the local-ear mechanism** and identify the missing global information.
Do not offer another restatement of the same unpaid ear inequality as
a new research target.

Parking this route is not refutation of Z184/E183. The next program
step can return to unrestricted E183 or a different discovery target;
do not initiate it yourself. The current assignment remains singular.

## Five-file proof-only evidence policy

Exclusive outputs:

- `frontier/iterations/i186-theta-region-balance.md`
- `frontier/experiments/i186_theta_region_balance/analytic-attempt.md`
- `frontier/experiments/i186_theta_region_balance/reading-and-failures.md`
- `frontier/experiments/i186_theta_region_balance/input-authentication.json`
- `frontier/sources/i186_theta_region_balance/literature.md`

No other writes, agents, ancestor/shared-ledger edits, staging, commits
or publication. No historical control rebuild/replay, copied snapshots
or new seal framework. Parent retains the existing sealed reference.
Preserve failed written routes and honest source-reading limits.

Authenticate all five I185 files before proof work:

| Output | SHA-256 |
| --- | --- |
| Report | `4021b5fb63fd9b4742dd7bcb9c35be2e33a492cac16d83654b3f8fb477310a9d` |
| Analytic attempt | `b2050c06cdf79dd9e863844a5432fbc337faad2375a1a961e6c7c94c96aa5fac` |
| Reading/failures | `13066230f26c5f1d3b2385d17e5ae6c8b66ddc969ddcc713f7f98aca77557827` |
| Input authentication | `f0151d4ccf4855576c9d3dd292328880f7150c1c951b10852189a630dd6f4e14` |
| Literature receipt | `cead5110dbb5003b34b5a86a5012154d17a5f01c042c10a383b9ef05ee20f7cf` |

Also hash this brief and the finalized I185 parent disposition. The
parent's inherited 23-stage replay passed in about 8.70 seconds,
with all strict bytes, memberships and eight probes checked. Those
controls and the twelve facial/626 matching cases remain finite.

Return exact original-target verdicts, full region argument, any
nontrivial consequence or precise gap, source dependencies/limits,
the continue-or-park recommendation under the stopping rule, and
detached hashes of all five outputs. This is an unsealed proof record.
Technical results do not increase the accepted count; substantial
candidates need independent correctness and contribution gates.
