# PARTIAL: actual local hazard and deterministic prefix-tree blocks

Solo implementation, 2026-10-30. Counts unchanged: 9 additional /39 total /next40. Root alone accepts/counts. No novelty or full-tail closure claim.

All thirteen inherited mathematical modules Literal through Assembly are byte-identical to frozen r8. LastSplit.lean is the only new mathematical module.

Closed endpoints in namespace LiteralGame:
- higher_duplicate_or_four and reachable_split_path: under n>=1 and N<F(n+1), a reachable board with >n+2 tokens admits an immediate split or C1,C1,S2. Positive indices and the certified index bound are used, with at most n-1 higher bins.
- actual_local_split_cylinder: some legal success word v has length 1..3, contains a split, and has actual cylinder mass ratio >=blockLower n. The ratio is literally actual_prefix_continuation, and every reciprocal legal-type factor uses the certified <=2n bound.
- actual_split_within_three and actual_no_split_one_block: exact actual finite-law split-soon mass >=p times prefix mass, and complementary no-split-soon mass <=(1-p) times prefix mass. The variable-length cylinder is included in the split-soon event; no fictitious three-step extension law is invoked. Short/terminal words are included in the complement, making this a valid upper bound.
- actual_deterministic_block_induction and actual_fixed_deterministic_blocks: the actual finite prefix-tree mass of q consecutive three-move no-split blocks, retaining high-token starts, is <=(1-p)^q at every fixed r. Each edge is an existing complete-word prefix of the required length; children have disjoint cylinders. Low-token/terminal starts exit with zero contribution. No conditional independence, hazard premise, Markov law or conditioning at a random time is used.
- long_combine_suffix_high: if an executed combine-only suffix has length >3q+n+3, then at every position 3j with j<=q its board has >n+2 tokens. This is a pointwise consequence of exact token decrement, including a possibly empty terminal board.
- nonexistent_prefix_zero explicitly gives zero actual mass to nonexistent prefixes.

REMAINING GAP: The requested literal lastSplit statistic and its one-based/zero convention are not yet defined in Lean. The equality/inclusion between the recursive prefix-tree mass and the literal complete-word survivor event, the fact that every letter after the last split is a combine, and the final union over r=0..3N have not been certified. Therefore the requested suffixTailMass <=(3N+1)*(1-p)^q endpoint is NOT delivered. The deterministic high-token lemma is available for that bridge; it is not presented as the final event inclusion.

Boundary scope: q=0 is included in the formal block induction (tree base is cylinderMass, forest base <=1). No N>0 or F(n)<=N premise is used. For N=0 the local high-token hypothesis is impossible, while prefix-tree bounds still hold; completeDomain_zero and P_zero are inherited. Short words are excluded from positive-length child levels, rather than renormalized. No-split words would be covered at r=0 in the intended final union, but that union and the strict suffix event remain unproved. Strict >3q+n+3 is retained in the pointwise lemma; >= is not substituted.

Audit/replay/final receipts are authoritative for verification of the delivered partial endpoints only. No asymptotics, sigma-algebra construction, all-N limit, final mixing, manuscript or acceptance claim.
