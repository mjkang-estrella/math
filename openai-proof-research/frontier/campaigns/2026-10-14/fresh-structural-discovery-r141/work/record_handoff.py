from research import *
rels=['frontier/iterations/i13-fresh-discovery.md','frontier/iterations/i24-elementary-unimodality-resumed.md','frontier/campaigns/2026-10-14/fresh-structural-discovery-r8/candidate.md','frontier/campaigns/2026-10-14/elementary-unimodality-r2/candidate.md']
for r in rels:assert not any(forbidden(c) for c in pathlib.PurePosixPath(r).parts)
save('history-bindings.json',[bind(r) for r in rels])
readlog={
 'recorded_utc':now(),
 'timing':'Retrospective extent log. Exact acquisition/binding/search-completion times are in their receipts. This timestamp is not a reconstructed start time or a claim that every acquired byte was read.',
 'context':{'AGENTS.md':'full; reread at handoff','sources/upstream.json':'full','sources/preprints-tree.json':'parsed complete 13223 entries; navigation/authentication only; nontruncated SHA matched','sources/CONTENTS.md':'catalogue navigation, not semantic clearance','research-brief-2026-10-20.txt':'full earlier; relevant scope/rights clauses reread at handoff; only obsolete campaign/model lines overridden','NEW-TEN-2026-10-14.md':'lines 1-110 acceptance rules and context','r140 parent contribution-r1-disposition.md':'full','r140 parent contribution-r1-adoption/adoption.json':'initial combined display partly truncated; full 36-line copy reread at handoff','r140 parent contribution-r1-adoption/replay.json':'full separately','t205q140 packet/public/review.md':'full separately after earlier combined truncation','t205q140 packet/public/reading-limits.md':'full','t205q140 envelope files':'hash authentication, not their full payload replay'},
 'pinned_read_extents':{
 'Elementary-Positivity/01-introduction.tex':'full',
 'Elementary-Positivity/02-graphs.tex':'full',
 'Elementary-Positivity/03-reordering.tex':'1-210; remaining label/navigation matches only',
 'Elementary-Positivity/04-walls.tex':'1-210 and 215-480; no claim on omitted gap or later material',
 'Elementary-Positivity/05-triangle.tex':'1-230',
 'Elementary-Positivity/06,07':'acquired, not read',
 'Common-Integer-Polymatroid/introduction.tex':'full; exact input/thm:main reread at handoff',
 'Common-Integer-Polymatroid/polyhedra.tex':'full 1-417 across earlier split reads; 1-320 reread for base calculus and integrality',
 'Common-Integer-Polymatroid/signatures.tex':'full in initial research; 1-270 reread for general balanced summation',
 'Common-Integer-Polymatroid/counting.tex':'1-385 and 480-625; intervening and later sections not fully read. Full transport proposition and noisy-evaluation coupling body read.',
 'Common-Integer-Polymatroid/geometry.tex':'1-220; initial partition and shift-average statement, not whole enlargement proof',
 'Common-Integer-Polymatroid/ports.tex':'1-140; integral tree-coordinate operation, not whole smoothing/volume argument',
 'Common-Integer-Polymatroid/evaluation.tex':'acquired, not read',
 'Approximate-counting-common-matroid-bases/build/main.tex':'245-420; full paired rank reduction and two polynomial signature setup; coefficient proof only beginning. Other labels navigation only.',
 'Cell-Bounded-Contingency-Tables/signatures.tex':'82-200 and 302-420: binary contractions and pair inequalities with proof; two factorial lifts read in polymatroid source, not full companion section',
 'Cell-Bounded-Contingency-Tables/transport.tex':'full, across split reads covering 1-end; finite signed transport, defect means, observable variance, time averages and trace return proof',
 'Other acquired README, main, bibliography, figure and section files':'acquired/authenticated; not semantic reads unless separately identified above'
 },
 'primary_read_extents':{
 'chen-liu-v1.txt':'1-465;1120-1420;2100-2228;3735-3815. Actual v1: main convolution/curvature interfaces and selected proofs, C.23 and adjoining C.22 tail. Not all applications/proofs read.',
 'davison-mandel.txt':'1800-1910: Theorem 2.15 and proof, Conjecture 2.17 and acyclic Theorem 2.18 statement. Acyclic proof body not read; never used as a proved new bridge.',
 'branden-huh.txt':'1835-2055;2440-2570. Includes Lemma 3.24 and Proposition 3.25 with proofs and Theorem 4.10 with full proof. Other portions acquired only.',
 'goemans-union.txt':'full two-page author lecture proof. Displayed Theorem 4 prints X on left but E on right; body proves full-ground formula. Restricted formula follows by restricting the matroids, not by copying the displayed typo.',
 'edmonds-fulkerson-1965':'acquisition failed HTTP403 and web timeout; metadata only; no body read',
 'Edmonds1970':'bounded search metadata/citations only; original body not acquired. Used source full greedy/calculus and integral two-chain proof instead.'
 },
 'history':{'I13':'full relevant section 2B and section4; earlier section1-2 read. Other sections partial incidental displays, not relied upon. Original full file copied only for current-byte binding.','I24':'combined display truncated; visible first sections only. Navigation establishes prior overlapping target; no full correctness assessment.','r8 candidate':'1-210 only; full bytes late copied, not full semantic read','elementary-unimodality-r2 candidate':'combined display partly clipped; not a full semantic read','i22,i60,r14,r46,r66,r113':'focused rg matches with two context lines only; navigation, not full bodies','other search hits':'filename/navigation only, not clearance'},
 'scope_limits':['No T205 author scope/proof overlap: neither character ratios nor transposition-chain claims resumed; no author correctness audit.','No worldwide priority, current-open, full-corpus or companion-exhaustion assertion.','No independent mathematical gates; all artifact checks are byte/inventory checks.']}
save('read-ledger.json',readlog)
chron={'recorded_utc':now(),'events':[
 {'time_source':'context-bindings.json','event':'14 named originals bound after initial reads; no historical whole-parent snapshot'},
 {'time_source':'source/polymatroid/primary acquisition receipts','event':'169 screen; then I13 projection feasibility and actual source/primary proof interfaces'},
 {'time_source':'search/history-search.json and search/polymatroid-search.json','event':'completed before prospective isolation update; later exclusion patterns not retroactively claimed'},
 {'time_source':'isolation-update.json','event':'22:36:30.274773+00:00 policy recording; new patterns added before subsequent traversal. Exact user receipt instant is not reconstructed.'},
 {'time_source':'bh-acquisition.json','event':'classical coefficient-power closure read after initial fractional-power feasibility; no target frozen'},
 {'time_source':'search/projection-search.json','event':'later focused projection scan uses all six forbidden component/filename patterns; mutable task observations are routing only'},
 {'time_source':'union-acquisition.json and handoff writing','event':'late exact union/contraction lead generalized to rank oracle (1); paid source operations close the proposed uniform-support representation. No full nominee frozen.'},
 {'time_source':'projection-computation.json','event':'finite exact arithmetic comparisons agree; not proof or contribution gates'},
 {'time_source':'history-bindings.json','event':'four relevant history originals copied and hashed late, after reads; contemporary binding only'}],
 'initial_navigation_error':'First rg --files globs did not prune every depth and displayed excluded t088p133 and analytic-r133 filenames. No excluded body was opened by that command. Replaced with component-pruned traversal. No retrospective correction of that fact.',
 'preservation_scope':'Only named bytes bound in context/history receipts can be compared; no initial whole-root snapshot or claim about unrelated concurrent parent/lanes.'}
save('chronology.json',chron)
print('recorded current history bindings and honest read/chronology limits')
