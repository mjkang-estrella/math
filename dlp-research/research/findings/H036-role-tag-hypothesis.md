# H036 competent merged-role baseline hypothesis

Status: root PAPER hypothesis; mathematical review completed, cost review live.
No source change, solver run, or new implementation admitted. H034's cap remains
consumed. This is a competent-comparator check, not a claimed new attack.

The previous H034 cost gate leaves Delta=LC-LB unknown, partly because the
candidate queries/inserts one archive while split-role H019 loads an opposite
query head and a separate own-role insertion head. A merged H019 archive could
remove the second load: use H total heads, tag every record by baby/giant role,
scan one chain for the first opposite-role exact match, then prepend using the
already loaded head. Same-role equality is deliberately ignored. The geometric
inspection schedule, recovery and deterministic signed coverage are unchanged.

Root's proposed leading-count argument, NOT YET accepted:

- Split archives have H/2 heads each; approximately T²/4 opposite-role pairs
  have collision probability beta(p,H/2)~2/H.
- A merged archive has approximately T²/2 prior pairs with probability
  beta(p,H)~1/H. Thus each has expected leading node visits q/(2H), using
  H019's E[T²]~q under uniform full-range targets and H=Theta(sqrt(q)).
- Merged same-role visits can check role before reading/comparing the key;
  approximately half the visited records are then cheaper. Tags, masks,
  branches and pointer traffic must still be paid. Packing a tag in an existing
  word requires an explicit width/layout argument, not a free bit assumption.
- Exact same-role coincidences violate the distinct-key hash formula. Baby
  abscissae are unique in the short prefix. Giant equality for j!=j' requires
  2k=(j+j')D modulo q, probability1/q over uniform k. The deterministic cap
  has O(q) possible pairs, so their expected count is O(1), even after stopping.
- Terminal partial chains omit at most O(T) pairs, ordinarily O(T/H)=O(1)
  expected probes; exceptional same-role equalities need the preceding bound.

If this survives, the earlier extra-head-read argument cannot establish a
candidate advantage against this alternative. It does not settle Delta or
complete work: merged role-check traffic differs, allocation/release may cost
more for the candidate's3sqrt(q) node cap than H019'ssqrt(2q), and the baseline
can spend spare peak on more heads. All of these require a complete ledger.

Review assignments, disjoint and read-only:
- Native Astra /root/h007_additive_relations: stopped mixed-role probability,
  equality exceptions, conditional trace and traffic counts only.
- Native Sol /root/h034_c4_implementation: full symbolic canonical-RAM ledger
  for H034 thickened graph versus H019 (split and merged) at matched capacities;
  charge leading allocation/release and identify any open positive price regime.

No hardware rates, arbitrary weighting victory, strongest-baseline dominance or
validated full-size improvement follows from a favorable symbolic regime.
Best supported exponent remains1/2; verified improvement NONE.

## Independent mathematical review result

Native Astra completed the review. For each query, truncate at the newest
OPPOSITE-role exact match. Partition preceding eligible records into unequal
opposite-role C_j, unequal same-role S_j, and equal same-role Z_j. Then exactly

    E[nonterminal merged probes | trace]
      = sum_j [beta(p,H)*(|C_j|+|S_j|)+|Z_j|].
    E[nonterminal split probes | trace]
      = sum_j beta(p,H/2)*|C_j|.

The terminal cross-role match contributes one additional deterministic probe.
The separate deterministic Z term repairs the naive all-pairs beta argument.
For uniform full-range k, expected Z over the stopped trace is O(1), by the
fixed-cap giant-pair calculation above. Per-index role balance gives each
role-pair class T²/4+O(T), after the terminal-chain truncation. With the reviewed
moment E[T²]=q+O(sqrt(q)), p comparable to q and H=Theta(sqrt(q)),

    E[merged nonterminal probes] = E[split nonterminal probes]
      = q/(2H)+O(1)

where equality here denotes the shared leading expression, not equality of
their exact expectations. Merged same-role probes total q/(4H)+O(1).
Approximately half can skip key work only in a layout supporting role-first
access; a whole-record read does not save that read. Role and pointer widths,
bit extraction, branches and next-pointer work remain charged. The next pointer
may need an additional bit compared with a separately sized role arena.
Sequential insertion validly reuses the original query-head value. These
statements exclude hash-dependent censorship and nonuniform-target substitution.

Decision: remove any presumed structural extra-head-read disadvantage from the
strongest enumerated H019 comparator. Await complete prices; no dominance claim.
