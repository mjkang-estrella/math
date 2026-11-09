# Sym2: remaining high-dimensional persistence configurations

**COMPUTED** labels executed finite searches and counts. **PROVED (checked)** labels complete certificate and slice-cover replays. BUDGET is still open; these computations do not settle multiplicative persistence.

## Exact assignment after codex, codex3a, codex3b and sym

The `codex/results_t14112.json` universe contains 870 configurations. The union of its CLOSED records, codex3a CLOSED, codex3b CLOSED and sym closed keys has 339 keys. The exact complement has 531 keys. Source snapshots and SHA-256 hashes are in `sym2/inputs/` and `assignment.json`.

The 210 cases in dimensions 6–8 match `sym/summary.json` BUDGET exactly. The complement additionally contains 8 dimension-4, 311 dimension-5 and 2 dimension-9 cases. The dimension-9 cases are included rather than silently excluded. The last open target-32 configuration is `11|9,9,9` (dimension 4, K=98, initial qmin=3).

### Target 14112, dimension 4: 8 assigned

```text
136|45,45,54
237|18,54,54
307|54,54,72
536|9,45,54
616|27,45,45
636|9,45,45
656|9,27,45
676|18,18,27
```

### Target 14112, dimension 5: 311 assigned

```text
101|54,54,63,72
103|27,54,54,72
105|18,54,54,63
105|27,45,54,54
107|18,45,54,54
107|9,54,54,72
110|54,54,63,72
112|27,45,54,54
113|18,45,54,54
113|9,54,54,72
116|18,18,54,63
116|18,27,45,54
116|9,27,54,72
116|9,45,45,54
117|18,18,54,54
118|9,27,54,54
11|54,54,63,72
121|18,54,54,63
121|27,45,54,54
125|9,27,54,54
12|45,54,54,63
130|27,54,54,72
130|45,45,54,54
131|18,45,54,54
131|9,54,54,72
132|18,27,54,54
132|9,45,54,54
135|9,18,54,54
136|18,18,27,54
136|9,18,45,54
136|9,9,54,72
138|9,9,54,54
13|27,54,54,72
13|45,45,54,54
150|18,54,54,63
150|27,45,54,54
152|9,27,54,54
153|9,18,54,54
156|9,18,27,54
156|9,9,45,54
15|18,54,54,63
15|27,45,54,54
161|18,18,54,63
161|18,27,45,54
161|9,27,54,72
161|9,45,45,54
165|9,18,27,54
165|9,9,45,54
16|18,45,54,63
16|27,27,54,72
16|27,45,45,54
16|9,54,63,72
170|18,45,54,54
170|9,54,54,72
172|9,18,54,54
176|9,18,18,54
17|18,45,54,54
17|9,54,54,72
181|9,27,54,54
183|9,9,54,54
18|27,27,54,54
18|9,54,54,63
201|45,54,54,63
205|27,27,54,54
205|9,54,54,63
210|45,54,54,63
211|18,54,54,63
211|27,45,54,54
212|27,27,54,54
212|9,54,54,63
213|18,27,54,54
213|9,45,54,54
215|9,27,54,54
216|18,27,27,54
216|9,18,54,63
216|9,27,45,54
217|9,18,54,54
21|45,54,54,63
221|27,27,54,54
221|9,54,54,63
223|9,27,54,54
227|9,9,54,54
230|18,54,54,63
230|27,45,54,54
232|9,27,54,54
233|9,18,54,54
236|9,18,27,54
236|9,9,45,54
23|18,54,54,63
23|27,45,54,54
250|27,27,54,54
250|9,54,54,63
251|9,27,54,54
253|9,9,54,54
256|9,9,27,54
25|27,27,54,54
25|9,54,54,63
261|18,27,27,54
261|9,18,54,63
261|9,27,45,54
263|9,18,27,54
263|9,9,45,54
265|9,9,27,54
267|9,9,18,54
270|18,27,54,54
270|9,45,54,54
272|9,9,54,54
276|9,9,18,54
27|18,27,54,54
27|9,45,54,54
301|27,54,54,72
301|45,45,54,54
303|18,45,54,54
303|9,54,54,72
305|18,27,54,54
305|9,45,54,54
307|18,18,54,54
30|54,54,63,72
310|27,54,54,72
310|45,45,54,54
312|18,27,54,54
312|9,45,54,54
313|18,18,54,54
316|18,18,27,54
316|9,18,45,54
316|9,9,54,72
318|9,9,54,54
321|18,27,54,54
321|9,45,54,54
325|9,9,54,54
32|18,54,54,63
32|27,45,54,54
330|18,45,54,54
330|9,54,54,72
331|18,18,54,54
332|9,18,54,54
336|9,18,18,54
33|18,45,54,54
33|9,54,54,72
350|18,27,54,54
350|9,45,54,54
352|9,9,54,54
356|9,9,18,54
361|18,18,27,54
361|9,18,45,54
361|9,9,54,72
365|9,9,18,54
36|18,18,54,63
36|18,27,45,54
36|9,27,54,72
36|9,45,45,54
370|18,18,54,54
37|18,18,54,54
38|9,27,54,54
501|18,54,54,63
501|27,45,54,54
503|18,27,54,54
503|9,45,54,54
505|9,27,54,54
507|9,18,54,54
50|45,54,54,63
510|18,54,54,63
510|27,45,54,54
512|9,27,54,54
513|9,18,54,54
516|9,18,27,54
516|9,9,45,54
51|18,54,54,63
51|27,45,54,54
521|9,27,54,54
52|27,27,54,54
52|9,54,54,63
530|18,27,54,54
530|9,45,54,54
531|9,18,54,54
532|9,9,54,54
536|9,9,18,54
53|18,27,54,54
53|9,45,54,54
550|9,27,54,54
55|9,27,54,54
561|9,18,27,54
561|9,9,45,54
56|18,27,27,54
56|9,18,54,63
56|9,27,45,54
570|9,18,54,54
57|9,18,54,54
5|45,54,54,63
601|18,45,54,63
601|27,27,54,72
601|27,45,45,54
601|9,54,63,72
605|18,27,27,54
605|9,18,54,63
605|9,27,45,54
610|18,45,54,63
610|27,27,54,72
610|27,45,45,54
610|9,54,63,72
611|18,18,54,63
611|18,27,45,54
611|9,27,54,72
611|9,45,45,54
612|18,27,27,54
612|9,18,54,63
612|9,27,45,54
613|18,18,27,54
613|9,18,45,54
613|9,9,54,72
615|9,18,27,54
615|9,9,45,54
616|18,18,27,27
616|9,18,18,63
616|9,18,27,45
616|9,9,27,72
616|9,9,45,45
617|9,18,18,54
618|9,9,27,54
61|18,45,54,63
61|27,27,54,72
61|27,45,45,54
61|9,54,63,72
621|18,27,27,54
621|9,18,54,63
621|9,27,45,54
623|9,18,27,54
623|9,9,45,54
625|9,9,27,54
627|9,9,18,54
630|18,18,54,63
630|18,27,45,54
630|9,27,54,72
630|9,45,45,54
632|9,18,27,54
632|9,9,45,54
633|9,18,18,54
636|9,18,18,27
636|9,9,18,45
636|9,9,9,72
638|9,9,9,54
63|18,18,54,63
63|18,27,45,54
63|9,27,54,72
63|9,45,45,54
650|18,27,27,54
650|9,18,54,63
650|9,27,45,54
651|9,18,27,54
651|9,9,45,54
652|9,9,27,54
653|9,9,18,54
655|9,9,9,54
656|9,9,18,27
656|9,9,9,45
65|18,27,27,54
65|9,18,54,63
65|9,27,45,54
661|18,18,27,27
661|9,18,18,63
661|9,18,27,45
661|9,9,27,72
661|9,9,45,45
663|9,18,18,27
663|9,9,18,45
665|9,9,18,27
665|9,9,9,45
667|9,9,18,18
670|18,18,27,54
670|9,18,45,54
670|9,9,54,72
672|9,9,18,54
676|9,9,18,18
67|18,18,27,54
67|9,18,45,54
67|9,9,54,72
681|9,9,27,54
701|18,45,54,54
701|9,54,54,72
703|18,18,54,54
705|9,18,54,54
70|27,54,54,72
70|45,45,54,54
710|18,45,54,54
710|9,54,54,72
712|9,18,54,54
716|9,18,18,54
721|9,18,54,54
72|18,27,54,54
72|9,45,54,54
730|18,18,54,54
73|18,18,54,54
750|9,18,54,54
761|9,18,18,54
76|18,18,27,54
76|9,18,45,54
76|9,9,54,72
78|9,9,54,54
801|27,27,54,54
801|9,54,54,63
810|27,27,54,54
810|9,54,54,63
811|9,27,54,54
813|9,9,54,54
816|9,9,27,54
81|27,27,54,54
81|9,54,54,63
830|9,27,54,54
861|9,9,27,54
863|9,9,9,54
870|9,9,54,54
```

### Target 14112, dimension 6: 132 assigned

```text
101|18,18,54,54,63
101|18,27,45,54,54
101|9,27,54,54,72
101|9,45,45,54,54
103|18,18,27,54,54
103|9,18,45,54,54
103|9,9,54,54,72
105|9,18,27,54,54
105|9,9,45,54,54
107|9,18,18,54,54
10|27,45,45,54,54
113|9,18,18,54,54
11|18,18,54,54,63
11|18,27,45,54,54
11|9,27,54,54,72
11|9,45,45,54,54
121|9,18,27,54,54
121|9,9,45,54,54
125|9,9,9,54,54
131|9,18,18,54,54
13|18,18,27,54,54
13|9,18,45,54,54
13|9,9,54,54,72
150|9,18,27,54,54
150|9,9,45,54,54
152|9,9,9,54,54
15|9,18,27,54,54
15|9,9,45,54,54
161|9,18,18,27,54
161|9,9,18,45,54
161|9,9,9,54,72
165|9,9,9,18,54
17|9,18,18,54,54
181|9,9,9,54,54
1|18,45,54,54,63
1|27,27,54,54,72
1|27,45,45,54,54
1|9,54,54,63,72
201|18,27,27,54,54
201|9,18,54,54,63
201|9,27,45,54,54
205|9,9,27,54,54
210|18,27,27,54,54
211|9,18,27,54,54
211|9,9,45,54,54
213|9,9,18,54,54
215|9,9,9,54,54
21|18,27,27,54,54
21|9,18,54,54,63
21|9,27,45,54,54
221|9,9,27,54,54
223|9,9,9,54,54
23|9,18,27,54,54
23|9,9,45,54,54
251|9,9,9,54,54
256|9,9,9,9,54
25|9,9,27,54,54
261|9,9,18,27,54
261|9,9,9,45,54
263|9,9,9,18,54
265|9,9,9,9,54
27|9,9,18,54,54
301|18,18,27,54,54
301|9,18,45,54,54
301|9,9,54,54,72
303|9,18,18,54,54
305|9,9,18,54,54
30|9,45,45,54,54
310|18,18,27,54,54
310|9,18,45,54,54
321|9,9,18,54,54
330|9,18,18,54,54
33|9,18,18,54,54
361|9,9,18,18,54
36|9,18,18,27,54
36|9,9,18,45,54
501|9,18,27,54,54
501|9,9,45,54,54
503|9,9,18,54,54
505|9,9,9,54,54
51|9,18,27,54,54
51|9,9,45,54,54
521|9,9,9,54,54
52|9,9,27,54,54
53|9,9,18,54,54
55|9,9,9,54,54
561|9,9,9,18,54
5|18,27,27,54,54
5|9,18,54,54,63
5|9,27,45,54,54
601|18,18,27,27,54
601|9,18,18,54,63
601|9,18,27,45,54
601|9,9,27,54,72
601|9,9,45,45,54
605|9,9,18,27,54
605|9,9,9,45,54
610|18,18,27,27,54
610|9,18,18,54,63
610|9,18,27,45,54
611|9,18,18,27,54
611|9,9,18,45,54
611|9,9,9,54,72
613|9,9,18,18,54
615|9,9,9,18,54
61|18,18,27,27,54
61|9,18,18,54,63
61|9,18,27,45,54
61|9,9,27,54,72
61|9,9,45,45,54
621|9,9,18,27,54
621|9,9,9,45,54
623|9,9,9,18,54
625|9,9,9,9,54
63|9,18,18,27,54
63|9,9,18,45,54
63|9,9,9,54,72
651|9,9,9,18,54
65|9,9,18,27,54
65|9,9,9,45,54
661|9,9,18,18,27
661|9,9,9,18,45
661|9,9,9,9,72
663|9,9,9,18,18
665|9,9,9,9,18
67|9,9,18,18,54
681|9,9,9,9,54
701|9,18,18,54,54
801|9,9,27,54,54
811|9,9,9,54,54
81|9,9,27,54,54
861|9,9,9,9,54
```

### Target 14112, dimension 7: 58 assigned

```text
101|9,18,18,27,54,54
101|9,9,18,45,54,54
101|9,9,9,54,54,72
103|9,9,18,18,54,54
105|9,9,9,18,54,54
10|9,18,27,45,54,54
110|9,9,18,45,54,54
11|9,18,18,27,54,54
11|9,9,18,45,54,54
11|9,9,9,54,54,72
121|9,9,9,18,54,54
13|9,9,18,18,54,54
15|9,9,9,18,54,54
161|9,9,9,18,18,54
16|9,9,18,18,27,54
1|18,18,27,27,54,54
1|9,18,18,54,54,63
1|9,18,27,45,54,54
1|9,9,27,54,54,72
1|9,9,45,45,54,54
201|9,9,18,27,54,54
201|9,9,9,45,54,54
205|9,9,9,9,54,54
211|9,9,9,18,54,54
21|9,9,18,27,54,54
21|9,9,9,45,54,54
221|9,9,9,9,54,54
23|9,9,9,18,54,54
25|9,9,9,9,54,54
261|9,9,9,9,18,54
301|9,9,18,18,54,54
30|9,18,18,27,54,54
30|9,9,18,45,54,54
30|9,9,9,54,54,72
310|9,9,18,18,54,54
36|9,9,9,18,18,54
501|9,9,9,18,54,54
51|9,9,9,18,54,54
52|9,9,9,9,54,54
5|9,9,18,27,54,54
5|9,9,9,45,54,54
601|9,9,18,18,27,54
601|9,9,9,18,45,54
601|9,9,9,9,54,72
605|9,9,9,9,18,54
610|9,9,18,18,27,54
610|9,9,9,18,45,54
610|9,9,9,9,54,72
611|9,9,9,18,18,54
61|9,9,18,18,27,54
61|9,9,9,18,45,54
61|9,9,9,9,54,72
621|9,9,9,9,18,54
63|9,9,9,18,18,54
65|9,9,9,9,18,54
661|9,9,9,9,18,18
801|9,9,9,9,54,54
81|9,9,9,9,54,54
```

### Target 14112, dimension 8: 20 assigned

```text
101|9,9,9,18,18,54,54
10|9,9,18,18,27,54,54
10|9,9,9,18,45,54,54
10|9,9,9,9,54,54,72
110|9,9,9,18,18,54,54
11|9,9,9,18,18,54,54
12|9,9,9,9,18,54,54
16|9,9,9,9,18,18,54
1|9,9,18,18,27,54,54
1|9,9,9,18,45,54,54
1|9,9,9,9,54,54,72
201|9,9,9,9,18,54,54
210|9,9,9,9,18,54,54
21|9,9,9,9,18,54,54
30|9,9,9,18,18,54,54
50|9,9,9,9,18,54,54
5|9,9,9,9,18,54,54
601|9,9,9,9,18,18,54
610|9,9,9,9,18,18,54
61|9,9,9,9,18,18,54
```

### Target 14112, dimension 9: 2 assigned

```text
10|9,9,9,9,18,18,54,54
1|9,9,9,9,18,18,54,54
```

## Search and proof procedure

For an original key, K=9*S_low-1 and X=10^L+K+sum(c*10^q)=9*n. The far positions are pairwise distinct and satisfy 3<=q<L. Fixing a low position adds c*10^q to K. A terminal certificate has all remaining positions, and L, above its qmin floor, which guarantees v2(X)=v2(K). Raising that floor to at least v2(K)+3 makes the mod-8 exponent pin valid; the split low branches and short-length scan supply the complete original cover.

The required generator, checker, coverage auditor and supporting scripts were copied from sym into sym2. `gen_sym.py` and `check_sym.py` are byte-identical to those copied sources. All writes stay under `verification/highdim/sym2/` and this note; no git commit was made. All Python entrypoints use isolated stdlib Python under `ulimit -v 8000000`. Search/check commands are timeout-bounded below 30 minutes, and this continuation uses at most 12 concurrent computational workers.

Every assigned case is attempted in dimension order, with a barrier between dimensions. Searches checkpoint after every configuration and preserve every complete certificate atomically, including certificates from incomplete covers. Escalation reuses complete files, never partial trees. `input_*.json`, `search_*.json` and logs record budgets, schedules, code hashes, frontiers and stopping reasons.

A late runtime check found that the historical default forkserver pool did not inherit the parent process's cross-stage certificate index. Same-stage files could be reused, but the cross-stage cache was ineffective, causing redundant work. All generated files were retained and directly checked. The driver now requests a fork context explicitly; an actual search-worker test confirms hash-protected cache reuse (`cache_test_results.json`). A final bounded cache-recovery pass targets only unfinished configurations that had already saved complete pieces (`recovery_selection.json`); it does not relax certificate or coverage checks. Historical timings and certificate counts include the redundant work.

The hybrid refinement is already the nd-sym representation: each distinct coefficient is a separate group/coordinate, and each repeated-coefficient group is a multiset. Only permutations within an equal-coefficient group are identified. Distinct coefficient groups are never exchanged, so every distinct far coefficient ordering is covered. Each CLOSED configuration records its number of distinct coefficient words, k! / product(m_c!), in the coverage ledger.

An additional independent combinatorial audit enumerates all 19923 distinct coefficient words over the 532 assignments. For each word it verifies the bijection to coefficient-group position ranks and back, with no exchanged or lost distinct coefficients. Replacing ranks by arbitrary increasing positions proves coverage of each entire ordering cone. Per-configuration counts and word-stream hashes are in `ordering_audit.json`.

`gen_precomputed.py` adds search-only memoization and precomputes the decimal orbit {10^(g*j) mod p}, where g=gcd(M,ord_p(10)). Each coefficient contribution is its exact residue coset c*10^(q mod g) times this orbit. The existing independent sumset overapproximation and unchanged checker establish acceptance. Cached forbidden tests retain both exact exponent signatures; free lower bounds may be omitted from the key only with decimal-tail cosets, whose finite subgroup image is independent of the lower bound. `precompute_test_results.json` records equivalence and exact orbit checks.

Every retained certificate, including partial-cover components and inherited components actually reused, is replayed by a direct subprocess invocation of copied `check_sym.py` with brute L<=10. The checker is invoked as a CLI, without a wrapper import or monkeypatch. Commands, hashes, verdicts and timings are in `standalone_checks.json`. All retained certificates use nd-sym format, so the legacy-format condition for `verification/v14_checknd_hd.py` is inapplicable; no legacy-format certificate is presented as dual-checked.

Configuration closure is independently recomputed by the copied `audit_coverage.cover`, using only full-domain, hash-bound PASS certificates. If its enlarged cover is incomplete, a second independent replay in `coverage_distinct.py` tracks already fixed positions and discards a low branch only when that position is already fixed. Such a branch contradicts the original pairwise-distinct position domain. All viable low values and the high tail remain covered; free/free and free/fixed collision restrictions are still relaxed inside certificates. The state includes the fixed-position set, so different fixed sets are never silently merged. Per-closure coverage methods and skipped-branch counts are recorded. This is a coverage refinement, not a new arithmetic kill type.

For the higher-dimensional strong-floor pass, slicing instead decides successive positions p=3,4,...: either the position is empty (digit 1), or it contains one of the distinct remaining coefficient values, which is added to K and removed from the multiset. Advance p once in either case. Stop only when p >= max(3,v2(K)+3), and emit the remaining domain at floor p. Each original placement follows exactly one branch, positions cannot be fixed twice, and every coefficient ordering is covered. `position_cover` independently replays this containment from checked domains. A terminal certificate covers L>=p; all smaller lengths are included in the finite exception scan. Position-by-position slicing is also independently justified in Agent F's coverage write-up.

The distinct-fixed-position splitting invariant passes 72 independent small-box comparisons covering 780 labelled distinct points, including lengths below terminal floors. A separate exact enumeration of all 2/3/7-smooth integers below the largest finite exception bound checks the omitted short lengths. All size-leaf solutions are filtered back to the original target, low digits and far coefficient multiset; closure means a complete member list, not necessarily emptiness.

The position-by-position splitting invariant separately passes 72 small-box comparisons covering 585 canonical points. Coverage method counts are `{'original_enlarged_cover': 301, 'distinct_fixed_positions': 63, 'position_partition': 34}`.

## Executed results

- Target 32, dimension 4: 0 closed, 1 still open, 1 assigned.
- Target 14112, dimension 4: 8 closed, 0 still open, 8 assigned.
- Target 14112, dimension 5: 298 closed, 13 still open, 311 assigned.
- Target 14112, dimension 6: 85 closed, 47 still open, 132 assigned.
- Target 14112, dimension 7: 7 closed, 51 still open, 58 assigned.
- Target 14112, dimension 8: 0 closed, 20 still open, 20 assigned.
- Target 14112, dimension 9: 0 closed, 2 still open, 2 assigned.

Direct checker verdicts: {'PASS': 54777}. New retained search certificates: 54762; inherited components directly replayed again: 0; additional control/smoke files: 15.

The finite exception scan checks 53064 smooth integers through 33 digits, finding 1 members in the closed configurations. The complete member list is in `summary.json`.

Per-certificate kill dependencies and counts are in `kill_usage.json`; per-configuration unions are in `summary.json`. Dependencies conservatively include decimal-tail or mod-8 constraints whenever enabled and prime references occur, even if an individual witness could be reproved without them. Unaligned prime references are sumset kills; aligned references are ordinary residue/coset kills. Counts below count certificate dependencies or stored references, not omitted residue classes.

Alignment labels use independently verified exact decimal orders (stored per prime), with supply orders treated as untrusted hints. The order/classification helper passes 384 comparisons against finite decimal cycles, including exact, nonminimal, invalid and missing hints.

All retained/reused certificate dependency counts: `{'prime_coset': 54764, 'decimal_tail_coset': 54762, 'unaligned_sumset': 1415, 'exact_size': 59, 'mod8_parity': 45670}`.

All retained/reused stored reference counts: `{'aligned_prime_reference': 1081862, 'unaligned_sumset_reference': 5723, 'exact_size_leaf': 579}`.

Certificates actually used in full closures: 43689; dependency counts: `{'prime_coset': 43689, 'decimal_tail_coset': 43689, 'mod8_parity': 35063, 'unaligned_sumset': 1324, 'exact_size': 41}`; reference counts: `{'aligned_prime_reference': 1035885, 'unaligned_sumset_reference': 5195, 'exact_size_leaf': 560}`.

Agent F audit evidence seen at finalization is hash-listed in `summary.json` under `auditor_files`. If this list is empty, no indep4 report was present in this checkout. Checker acceptance is recorded separately from any independent soundness audit. A later invalidated kill type can be mapped to every affected certificate and configuration through these dependency ledgers.

Agent F independently confirms 121/121 prior sym certificates and reports no unsound kill type. Its verdict/proofs/coverage text and summary are frozen under `inputs/indep4/`. This is confirmation of the prior closures and kill-type arguments; it is not represented as an F-checker replay of the new sym2 certificates.

## Checkpointed search stages

- `search_broad8.json`: 532 attempts; {'COMPLETE_PENDING_CHECKS': 263, 'BUDGET': 269}; 2837.508 worker seconds; 607565913 partial lifts plus 202964286 completed-job lifts.
- `search_cache_recovery8.json`: 38 attempts; {'BUDGET': 34, 'COMPLETE_PENDING_CHECKS': 4}; 294.398 worker seconds; 17682254 partial lifts plus 5965018 completed-job lifts.
- `search_floor72.json`: 55 attempts; {'COMPLETE_PENDING_CHECKS': 42, 'BUDGET': 13}; 1016.334 worker seconds; 11957707 partial lifts plus 15137806 completed-job lifts.
- `search_high_positions72.json`: 210 attempts; {'COMPLETE_PENDING_CHECKS': 86, 'BUDGET': 124}; 10980.819 worker seconds; 771185595 partial lifts plus 369073859 completed-job lifts.
- `search_precomputed24.json`: 269 attempts; {'BUDGET': 266, 'COMPLETE_PENDING_CHECKS': 3}; 6356.799 worker seconds; 681018022 partial lifts plus 444623 completed-job lifts.
- `search_target32_floor72.json`: 1 attempts; {'BUDGET': 1}; 5.819 worker seconds; 12084 partial lifts plus 0 completed-job lifts.
- `search_target32_period30.json`: 1 attempts; {'BUDGET': 1}; 23.683 worker seconds; 46948 partial lifts plus 0 completed-job lifts.

## Exact final still-open set

```text
14112:101|9,18,18,27,54,54
14112:101|9,27,54,54,72
14112:101|9,9,18,45,54,54
14112:101|9,9,9,18,18,54,54
14112:101|9,9,9,54,54,72
14112:103|9,18,45,54,54
14112:103|9,9,18,18,54,54
14112:103|9,9,54,54,72
14112:105|9,9,9,18,54,54
14112:10|9,18,27,45,54,54
14112:10|9,9,18,18,27,54,54
14112:10|9,9,9,18,45,54,54
14112:10|9,9,9,9,18,18,54,54
14112:10|9,9,9,9,54,54,72
14112:110|9,9,18,45,54,54
14112:110|9,9,9,18,18,54,54
14112:11|18,18,54,54,63
14112:11|18,27,45,54,54
14112:11|9,18,18,27,54,54
14112:11|9,27,54,54,72
14112:11|9,45,45,54,54
14112:11|9,9,18,45,54,54
14112:11|9,9,9,18,18,54,54
14112:11|9,9,9,54,54,72
14112:121|9,18,27,54,54
14112:121|9,9,9,18,54,54
14112:12|9,9,9,9,18,54,54
14112:13|18,18,27,54,54
14112:13|9,18,45,54,54
14112:13|9,9,18,18,54,54
14112:150|9,18,27,54,54
14112:150|9,9,45,54,54
14112:152|9,27,54,54
14112:152|9,9,9,54,54
14112:15|9,18,27,54,54
14112:15|9,9,9,18,54,54
14112:161|9,18,18,27,54
14112:161|9,9,9,18,18,54
14112:16|9,9,18,18,27,54
14112:16|9,9,9,9,18,18,54
14112:1|18,18,27,27,54,54
14112:1|9,18,18,54,54,63
14112:1|9,18,27,45,54,54
14112:1|9,54,54,63,72
14112:1|9,9,18,18,27,54,54
14112:1|9,9,27,54,54,72
14112:1|9,9,45,45,54,54
14112:1|9,9,9,18,45,54,54
14112:1|9,9,9,9,18,18,54,54
14112:1|9,9,9,9,54,54,72
14112:201|18,27,27,54,54
14112:201|9,9,18,27,54,54
14112:201|9,9,9,45,54,54
14112:201|9,9,9,9,18,54,54
14112:205|9,9,9,9,54,54
14112:210|9,9,9,9,18,54,54
14112:211|9,9,9,18,54,54
14112:215|9,9,9,54,54
14112:21|9,9,18,27,54,54
14112:21|9,9,9,45,54,54
14112:21|9,9,9,9,18,54,54
14112:232|9,27,54,54
14112:23|9,9,9,18,54,54
14112:256|9,9,27,54
14112:256|9,9,9,9,54
14112:25|9,9,9,9,54,54
14112:261|9,27,45,54
14112:261|9,9,18,27,54
14112:261|9,9,9,45,54
14112:261|9,9,9,9,18,54
14112:263|9,9,45,54
14112:303|9,18,18,54,54
14112:305|9,9,18,54,54
14112:30|9,18,18,27,54,54
14112:30|9,45,45,54,54
14112:30|9,9,18,45,54,54
14112:30|9,9,9,18,18,54,54
14112:30|9,9,9,54,54,72
14112:310|18,18,27,54,54
14112:310|27,54,54,72
14112:310|9,18,45,54,54
14112:310|9,9,18,18,54,54
14112:312|9,45,54,54
14112:330|9,18,18,54,54
14112:331|18,18,54,54
14112:36|9,18,18,27,54
14112:36|9,9,18,45,54
14112:36|9,9,9,18,18,54
14112:501|9,9,9,18,54,54
14112:503|9,9,18,54,54
14112:50|9,9,9,9,18,54,54
14112:51|9,9,9,18,54,54
14112:52|9,9,27,54,54
14112:52|9,9,9,9,54,54
14112:5|9,9,18,27,54,54
14112:5|9,9,9,9,18,54,54
14112:601|9,18,18,54,63
14112:601|9,18,27,45,54
14112:601|9,9,18,18,27,54
14112:601|9,9,27,54,72
14112:601|9,9,9,18,45,54
14112:601|9,9,9,9,18,18,54
14112:601|9,9,9,9,54,72
14112:605|9,9,18,27,54
14112:605|9,9,9,45,54
14112:605|9,9,9,9,18,54
14112:610|18,18,27,27,54
14112:610|27,45,45,54
14112:610|9,18,18,54,63
14112:610|9,18,27,45,54
14112:610|9,9,18,18,27,54
14112:610|9,9,9,18,45,54
14112:610|9,9,9,9,18,18,54
14112:610|9,9,9,9,54,72
14112:611|9,9,9,18,18,54
14112:615|9,9,9,18,54
14112:61|18,18,27,27,54
14112:61|9,9,18,18,27,54
14112:61|9,9,9,9,18,18,54
14112:621|9,27,45,54
14112:621|9,9,18,27,54
14112:621|9,9,9,45,54
14112:623|9,9,9,18,54
14112:63|9,18,18,27,54
14112:63|9,9,18,45,54
14112:63|9,9,9,18,18,54
14112:65|9,9,9,9,18,54
14112:661|9,9,18,18,27
14112:661|9,9,9,9,18,18
14112:663|9,9,18,45
14112:801|9,54,54,63
14112:801|9,9,9,9,54,54
14112:81|9,54,54,63
32:11|9,9,9
```

The exact newly closed set, complete slice covers, member lists, coefficient ordering counts and kill dependencies are in `summary.json`. `manifest.json` hashes the evidence and this note. All search BUDGET diagnostics are finite computation records, not impossibility claims.

## Direct reproduction commands

```sh
bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym2/continue_sym2.py reconcile'
timeout 1500 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym2/continue_sym2.py check --workers 12 --force-check'
timeout 1500 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym2/continue_sym2.py audit'
bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym2/finalize_sym2.py'
bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym2/verify_manifest.py'
```
