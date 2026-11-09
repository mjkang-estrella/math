# CLOSED: literal finite last-split suffix tail

Solo implementation, 2026-10-30. Counts unchanged: 9 additional /39 total /next40. Root alone accepts. Full-source and novelty HOLD; this is a narrow formal assembly certificate, not an acceptance or manuscript.

The fourteen inherited mathematical modules Literal through LastSplit are byte-identical to frozen r9. SuffixUnion.lean is the new mathematical module.

Exact endpoint in namespace LiteralGame:

`suffixTailMass_bound {N n : ℕ} (hn : 1≤n) (hN : N<F (n+1)) (q : ℕ) : suffixTailMass N n q ≤ (3*N+1 : ℕ) * (1-blockLower n)^q`

All quantities here are rational, with the natural prefactor explicitly cast to ℚ. `suffixTailMass` is the actual sum of `P N w` over completeDomain N satisfying the STRICT inequality `3*q+n+3 < w.length-lastSplit w`. T is w.length. No lower bound F(n)≤N or positivity assumption on N is used.

`lastSplit` is the one-based greatest split position, zero when none. `lastSplit_le`, `lastSplit_zero_iff`, `lastSplit_cut`, `split_position_le`, and `lastSplit_attained` certify both bounds and attainment; `after_lastSplit` proves every move in drop(lastSplit w) is a combine. `suffix_empty_iff` handles lastSplit=T exactly. The empty word has lastSplit=0. A nonempty no-split word also has lastSplit=0 and enters at deterministic r=0.

The missing source bridge is closed by `event_step`, `literal_event_mass`, and `fixed_literal_mass`. BlockEvent is a literal predicate on a complete word: at each start u, retain HighPrefix N n u, require three actual remaining letters, require no split in those letters, then advance to w.take(u.length+3). Its zero-block predicate is simply u.IsPrefix w. No tree mass is used in this event definition. `event_step` proves the actual disjoint child-cylinder partition, rather than assuming a correspondence. `literal_event_mass` identifies its actual finite mass with r9 blockTreeMass. At fixed r, disjoint initial cylinders give exactly fixedBlockMass. Short words cannot create missing children; nonexistent prefixes have empty cylinders and inherited zero mass.

`long_suffix_event` uses complete-word execution, r9 long_combine_suffix_high, and exact three-letter advances to put a sufficiently long combine-only suffix in the literal block event. `complete_length_le` handles positive N by the strict <3N theorem and N=0 separately. `suffix_tail_inclusion` places the tail event in the union over r in range(3*N+1), using r=lastSplit w pointwise only. The finite union bound and inherited actual_fixed_deterministic_blocks finish the endpoint. Never condition at lastSplit; no stopping-time or independence assumption is made.

Boundary scope: q=0 is included by the event base and inherited block induction, with bound 3*N+1. N=0 has exactly zero tail mass (`suffixTailMass_zero`). `short_word_excluded` handles T≤3q+n+3. Equality of tail length to 3q+n+3 is excluded by definition. No-split words, final-move splits, empty words, and nonexistent/short prefixes are covered by the exact definitions and lemmas above.

The optional zero-padded observability helper was deferred. No asymptotics, sigma-algebra, all-N limit, or final mixing conclusion is claimed. Audit/replay/final receipts report the verification counts and resource records. All failures are retained. No external retrieval, public edits, git operations, MathDB edits, manuscript edits, child agents, or shared-file writes.
