from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent
S=L/'frozen/sol-zeckendorf-concentration-assembly-formal-r8'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
refs=json.loads((S/'immutable-references.json').read_text())
for r in refs:assert sha(Path(r['original']))==r['sha256']==sha(Path(r['copy']))
(L/'immutable-references.json').write_text(json.dumps(refs,indent=2)+'\n')
rows=json.loads((L/'freeze.json').read_text())
for rel in ['Data/Finset/Defs.lean','Data/Multiset/Count.lean']:
 p=Path(json.loads((L/'pins.json').read_text())[0]['path'])/'Mathlib'/rel
 d=L/'frozen/library'/rel;d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes(p.read_bytes())
 rows.append(dict(original=str(p),copy=str(d.relative_to(L)),sha256=sha(p)))
(L/'freeze.json').write_text(json.dumps(rows,indent=2)+'\n')
(L/'SUMMARY.md').write_text('''# PARTIAL: actual local hazard and deterministic prefix-tree blocks

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
''')
(L/'RUN.md').write_text('''Run sh run.sh from this directory. Every Python helper is invoked through the fixed helper_guard.py with OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1. Lean is launched only by runner.py: verified compiler SHA, j1 M2700, warningAsError true, autoImplicit false, group RSS2800MiB CPU210 wall230. The fixed helper guard retains AS/groupRSS512MiB CPU210 wall230; only its explicitly approved Lean child has the separate Lean memory budget. No cap was raised beyond that approved exception.

Then guarded python certify.py pack; guarded python certify.py replay; guarded python certify.py manifest; in a SEPARATE invocation guarded python certify.py verify. Archive contains sources and harness only, with fixed ZIP metadata. Replay extracts into a fresh directory and compiles serially, then removes compiled objects throughout this lane. Manifest excludes itself and verification-receipt.json. Failed attempts and exact sources are retained outside the replay source archive.
''')
(L/'PROOF.md').write_text('''Implementation notes, not a manuscript. The mathematical proof is LastSplit.lean. A high-token board with no duplicate above index one is bounded by count(1) copies of index one plus one copy of each index 2..n; hence it has at least four ones. Two C1 moves make S2 legal. Along a legal success word of length k<=3 each reciprocal factor is >=a=(2n)^-1, so its product is >=a^k>=a^3. The normalized actual continuation cylinder supplies exactly that ratio, even for k=1. This cylinder is included in the split-soon event. Disjoint complementary finite sums yield the one-block contraction. Equal-length prefixes have disjoint complete-word cylinders. Summing their actual masses gives the finite prefix-tree contraction and induction. Remaining endpoint gaps are listed in SUMMARY.md.
''')
(L/'FAILURES.md').write_text('''Preserved attempts record syntax errors from missing spaces near numerals, multiset count/card rewrites, an induction that initially generalized irrelevant hypotheses, a nonexistent list lemma, and deprecated if_pos/if_neg names rejected by warningAsError. Lean generated an error diagnostic saying declaration uses sorry after a failed elaboration; no explicit sorry/admit was written, and the failed module was not accepted. Every accepted module is audited for all transitive axioms and unsafe/partial flags.

Procedure qualifications: initial broad administrative output was truncated; administrative JSON was then parsed under the guard. A bounded library declaration search exposed Count.lean snippets before that library snapshot; later full-file snapshots are recorded, not falsely described as freeze-first for those snippets. Scientific campaign sources were frozen before reading. No HTTP, browser, Google, git, MathDB, shared or public edits. Historical denied routes and inaccessible intervals remain parked; no live prior-art clearance asserted.

The final last-split inclusion/union and literal event equality remain unproved. This partial result receives no credit.
''')
(L/'PROOF-SOURCES.md').write_text('''Scientific campaign originals/copies were frozen before inspection and are verified before/after. Administrative files are snapshots only and are not treated as immutable shared files. Reused immutable PDF/text references avoid recursive historical duplication. The actual primary text is Cheigh et al., Towards the Gaussianity of Random Zeckendorf Games, arXiv:2210.11038v1, 2022-10-20; original/review conventions are frozen from r284 and its independent preliminary review. Primary PDF SHA 25b8427e43212e53fc2b031e3a6def4920ce76736cb6b063471dc89d0f474a01; text SHA 7226873f1b06c47ab1cfcd5ee035db73cd61e05988341e1e4bf0af92478ef12a. The formal new proof uses only inherited verified law/termination/token/index theorems, not a literature hazard assertion. Internal r8/r9 work is dated 2026-10-30, not public priority. All nine package pins and compiler hash are checked without git operations. Access limitations and freeze-order qualification are in FAILURES.md. No external retrieval or current registry assertion.
''')
(L/'provenance.json').write_text(json.dumps(dict(date='2026-10-30',status='PARTIAL',counts_changed=False,external_requests=0,scientific_freeze='freeze.json',immutable='immutable-references.json',remaining=['literal lastSplit','survivor event/tree correspondence','final deterministic union']),indent=2)+'\n')
(L/'bindings.json').write_text(json.dumps(dict(local='actual_split_within_three',contraction='actual_no_split_one_block',blocks='actual_fixed_deterministic_blocks',pointwise='long_combine_suffix_high',target_closed=False),indent=2)+'\n')
t=(S/'certify.py').read_text()
t=t.replace("assert sha(Path(r['original']))==r['sha256']==sha(L/r['copy']),r", "assert sha(L/r['copy'])==r['sha256'],r\n        if not r['copy'].startswith('administrative/'):\n            assert sha(Path(r['original']))==r['sha256'],r")
t=t.replace("'Tail','Concentration']", "'Tail','Concentration','Assembly']")
t=t.replace("'frozen/sol-zeckendorf-cell-concentration-formal-r7'", "'frozen/sol-zeckendorf-concentration-assembly-formal-r8'")
t=t.replace("'Concentration','Assembly'])", "'Concentration','Assembly','LastSplit'])")
t=t.replace("'Assembly.lean','Inventory.lean'", "'Assembly.lean','LastSplit.lean','Inventory.lean'")
t=t.replace("'Abundance', 'Tail', 'Concentration', 'Assembly']", "'Abundance', 'Tail', 'Concentration', 'Assembly', 'LastSplit']")
t=t.replace("attempt-013.log", "attempt-014.log").replace("attempt-014.log').read_text(),names", "attempt-015.log').read_text(),names")
t=t.replace('CLOSED: finite Bernoulli interval and actual finite interval/tail; no asymptotics or mixing claim','PARTIAL: actual local split hazard and deterministic prefix-tree blocks; final inclusion/union open')
(L/'certify.py').write_text(t)
print('immutable references verified; partial packet prepared')
