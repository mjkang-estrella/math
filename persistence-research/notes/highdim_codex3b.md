# Odd-index t=14112 continuation (codex3b)

Scope: zero-based odd indices 1,3,...,663 of the 665 lexicographically sorted BUDGET keys in `verification/highdim/codex/results_t14112.json`. Exactly 332 configurations. The parallel codex3a agent owns even indices and t=32. Only codex3b and this note are written; no commits.

Read the previous Codex report/notes and the final two sections of verification/REPORT.md. All closures require a full E/E2 slice cover, unordered certificates for >=3 far digits or every distinct coefficient ordering otherwise. Only ordinary prime kills and exact-size leaves are permitted. Every certificate used here will be executed directly through both original checkers with python3 -I, without monkeypatch wrappers.

## Exact assigned list

```text
1: 101|18,27,45,54,54
3: 101|9,18,18,27,54,54
5: 101|9,45,45,54,54
7: 101|9,9,9,18,18,54,54
9: 103|18,18,27,54,54
11: 103|45,45,54,54
13: 103|9,9,18,18,54,54
15: 105|18,54,54,63
17: 105|9,18,27,54,54
19: 105|9,9,9,18,54,54
21: 107|9,18,18,54,54
23: 10|18,18,27,27,54,54
25: 10|27,27,54,54,72
27: 10|9,18,18,54,54,63
29: 10|9,54,54,63,72
31: 10|9,9,27,54,54,72
33: 10|9,9,9,18,45,54,54
35: 10|9,9,9,9,54,54,72
37: 110|18,27,45,54,54
39: 110|9,18,18,27,54,54
41: 110|9,45,45,54,54
43: 110|9,9,9,18,18,54,54
45: 112|18,54,54,63
47: 112|9,18,27,54,54
49: 112|9,9,9,18,54,54
51: 113|9,18,18,54,54
53: 116|18,18,54,63
55: 116|9,18,18,27,54
57: 116|9,45,45,54
59: 116|9,9,9,18,18,54
61: 117|18,18,54,54
63: 118|9,9,9,54,54
65: 11|18,27,45,54,54
67: 11|9,18,18,27,54,54
69: 11|9,45,45,54,54
71: 11|9,9,9,18,18,54,54
73: 121|18,54,54,63
75: 121|9,18,27,54,54
77: 121|9,9,9,18,54,54
79: 125|9,9,9,54,54
81: 12|45,54,54,63
83: 12|9,27,45,54,54
85: 12|9,9,9,45,54,54
87: 130|18,18,27,54,54
89: 130|45,45,54,54
91: 130|9,9,18,18,54,54
93: 131|18,45,54,54
95: 131|9,54,54,72
97: 132|9,45,54,54
99: 133|18,18,54,54
101: 136|18,18,27,54
103: 136|9,18,45,54
105: 136|9,9,54,72
107: 13|18,18,27,54,54
109: 13|45,45,54,54
111: 13|9,9,18,18,54,54
113: 150|18,54,54,63
115: 150|9,18,27,54,54
117: 150|9,9,9,18,54,54
119: 152|9,9,9,54,54
121: 156|9,18,27,54
123: 156|9,9,9,18,54
125: 15|27,45,54,54
127: 15|9,9,45,54,54
129: 161|18,18,54,63
131: 161|9,18,18,27,54
133: 161|9,45,45,54
135: 161|9,9,9,18,18,54
137: 165|9,18,27,54
139: 165|9,9,9,18,54
141: 16|18,45,54,63
143: 16|27,45,45,54
145: 16|9,18,27,45,54
147: 16|9,9,18,18,27,54
149: 16|9,9,45,45,54
151: 16|9,9,9,9,18,18,54
153: 170|18,45,54,54
155: 170|9,54,54,72
157: 172|9,18,54,54
159: 17|18,45,54,54
161: 17|9,54,54,72
163: 181|9,9,9,54,54
165: 18|27,27,54,54
167: 18|9,9,27,54,54
169: 1|18,18,27,27,54,54
171: 1|27,27,54,54,72
173: 1|9,18,18,54,54,63
175: 1|9,54,54,63,72
177: 1|9,9,27,54,54,72
179: 1|9,9,9,18,45,54,54
181: 1|9,9,9,9,54,54,72
183: 201|45,54,54,63
185: 201|9,27,45,54,54
187: 201|9,9,9,45,54,54
189: 205|27,27,54,54
191: 205|9,9,27,54,54
193: 210|18,27,27,54,54
195: 210|9,18,54,54,63
197: 210|9,9,18,27,54,54
199: 210|9,9,9,9,18,54,54
201: 211|27,45,54,54
203: 211|9,9,45,54,54
205: 212|27,27,54,54
207: 212|9,9,27,54,54
209: 213|18,27,54,54
211: 213|9,9,18,54,54
213: 215|9,9,9,54,54
215: 216|9,18,54,63
217: 216|9,9,18,27,54
219: 216|9,9,9,9,18,54
221: 21|18,27,27,54,54
223: 21|9,18,54,54,63
225: 21|9,9,18,27,54,54
227: 21|9,9,9,9,18,54,54
229: 221|9,54,54,63
231: 221|9,9,9,9,54,54
233: 223|9,9,9,54,54
235: 230|18,54,54,63
237: 230|9,18,27,54,54
239: 230|9,9,9,18,54,54
241: 232|9,9,9,54,54
243: 236|9,18,27,54
245: 236|9,9,9,18,54
247: 23|18,54,54,63
249: 23|9,18,27,54,54
251: 23|9,9,9,18,54,54
253: 250|9,54,54,63
255: 250|9,9,9,9,54,54
257: 251|9,9,9,54,54
259: 256|9,9,27,54
261: 25|27,27,54,54
263: 25|9,9,27,54,54
265: 261|18,27,27,54
267: 261|9,27,45,54
269: 261|9,9,9,45,54
271: 263|9,18,27,54
273: 263|9,9,9,18,54
275: 265|9,9,9,9,54
277: 270|18,27,54,54
279: 270|9,9,18,54,54
281: 276|9,9,18,54
283: 27|9,45,54,54
285: 301|18,18,27,54,54
287: 301|45,45,54,54
289: 301|9,9,18,18,54,54
291: 303|18,45,54,54
293: 303|9,54,54,72
295: 305|9,45,54,54
297: 307|18,18,54,54
299: 30|18,18,54,54,63
301: 30|54,54,63,72
303: 30|9,27,54,54,72
305: 30|9,9,18,45,54,54
307: 30|9,9,9,54,54,72
309: 310|27,54,54,72
311: 310|9,18,45,54,54
313: 310|9,9,54,54,72
315: 312|9,45,54,54
317: 313|18,18,54,54
319: 316|9,18,45,54
321: 316|9,9,54,72
323: 321|18,27,54,54
325: 321|9,9,18,54,54
327: 32|18,54,54,63
329: 32|9,18,27,54,54
331: 32|9,9,9,18,54,54
333: 330|9,18,18,54,54
335: 331|18,18,54,54
337: 336|9,18,18,54
339: 33|9,18,18,54,54
341: 350|18,27,54,54
343: 350|9,9,18,54,54
345: 356|9,9,18,54
347: 361|9,18,45,54
349: 361|9,9,54,72
351: 36|18,18,54,63
353: 36|9,18,18,27,54
355: 36|9,45,45,54
357: 36|9,9,9,18,18,54
359: 370|18,18,54,54
361: 37|54,54,72
363: 38|9,27,54,54
365: 501|18,54,54,63
367: 501|9,18,27,54,54
369: 501|9,9,9,18,54,54
371: 503|9,45,54,54
373: 505|9,27,54,54
375: 507|9,18,54,54
377: 50|45,54,54,63
379: 50|9,27,45,54,54
381: 50|9,9,9,45,54,54
383: 510|18,54,54,63
385: 510|9,18,27,54,54
387: 510|9,9,9,18,54,54
389: 512|9,9,9,54,54
391: 516|9,18,27,54
393: 516|9,9,9,18,54
395: 51|27,45,54,54
397: 51|9,9,45,54,54
399: 521|9,27,54,54
401: 52|27,27,54,54
403: 52|9,9,27,54,54
405: 530|18,27,54,54
407: 530|9,9,18,54,54
409: 532|9,9,54,54
411: 536|9,9,18,54
413: 53|9,45,54,54
415: 550|9,27,54,54
417: 556|9,27,54
419: 55|9,27,54,54
421: 561|9,18,27,54
423: 561|9,9,9,18,54
425: 56|18,27,27,54
427: 56|9,27,45,54
429: 56|9,9,9,45,54
431: 570|9,18,54,54
433: 5|18,27,27,54,54
435: 5|9,18,54,54,63
437: 5|9,9,18,27,54,54
439: 5|9,9,9,9,18,54,54
441: 601|18,45,54,63
443: 601|27,45,45,54
445: 601|9,18,27,45,54
447: 601|9,9,18,18,27,54
449: 601|9,9,45,45,54
451: 601|9,9,9,9,18,18,54
453: 605|18,27,27,54
455: 605|9,27,45,54
457: 605|9,9,9,45,54
459: 610|18,18,27,27,54
461: 610|27,27,54,72
463: 610|9,18,18,54,63
465: 610|9,54,63,72
467: 610|9,9,27,54,72
469: 610|9,9,9,18,45,54
471: 610|9,9,9,9,54,72
473: 611|18,27,45,54
475: 611|9,27,54,72
477: 611|9,9,18,45,54
479: 611|9,9,9,54,72
481: 612|9,18,54,63
483: 612|9,9,18,27,54
485: 612|9,9,9,9,18,54
487: 613|9,18,45,54
489: 613|9,9,54,72
491: 615|9,9,45,54
493: 616|18,18,27,27
495: 616|9,18,18,63
497: 616|9,9,18,18,27
499: 616|9,9,45,45
501: 616|9,9,9,9,18,18
503: 617|9,18,18,54
505: 618|9,9,9,9,54
507: 61|18,45,54,63
509: 61|27,45,45,54
511: 61|9,18,27,45,54
513: 61|9,9,18,18,27,54
515: 61|9,9,45,45,54
517: 61|9,9,9,9,18,18,54
519: 621|18,27,27,54
521: 621|9,27,45,54
523: 621|9,9,9,45,54
525: 623|9,18,27,54
527: 623|9,9,9,18,54
529: 625|9,9,9,9,54
531: 630|18,18,54,63
533: 630|9,18,18,27,54
535: 630|9,45,45,54
537: 630|9,9,9,18,18,54
539: 632|9,18,27,54
541: 632|9,9,9,18,54
543: 636|9,18,18,27
545: 636|9,9,18,45
547: 636|9,9,9,72
549: 63|18,18,54,63
551: 63|9,18,18,27,54
553: 63|9,45,45,54
555: 63|9,9,9,18,18,54
557: 650|18,27,27,54
559: 650|9,27,45,54
561: 650|9,9,9,45,54
563: 651|9,18,27,54
565: 651|9,9,9,18,54
567: 652|9,9,9,9,54
569: 655|9,9,9,54
571: 656|9,9,18,27
573: 656|9,9,9,9,18
575: 65|9,18,54,63
577: 65|9,9,18,27,54
579: 65|9,9,9,9,18,54
581: 661|9,18,18,63
583: 661|9,9,18,18,27
585: 661|9,9,45,45
587: 661|9,9,9,9,18,18
589: 663|9,18,18,27
591: 663|9,9,9,18,18
593: 665|9,9,18,27
595: 665|9,9,9,9,18
597: 670|18,18,27,54
599: 670|9,9,18,18,54
601: 672|9,9,18,54
603: 676|9,18,45
605: 67|18,18,27,54
607: 67|9,9,18,18,54
609: 681|9,9,27,54
611: 701|18,45,54,54
613: 701|9,54,54,72
615: 705|9,18,54,54
617: 70|27,54,54,72
619: 70|9,18,45,54,54
621: 70|9,9,54,54,72
623: 710|9,18,18,54,54
625: 712|9,18,54,54
627: 716|9,54,72
629: 72|18,27,54,54
631: 72|9,9,18,54,54
633: 73|18,18,54,54
635: 761|9,18,18,54
637: 76|9,18,45,54
639: 76|9,9,54,72
641: 801|27,27,54,54
643: 801|9,9,27,54,54
645: 810|27,27,54,54
647: 810|9,9,27,54,54
649: 811|9,27,54,54
651: 813|9,9,54,54
653: 816|9,9,9,9,54
655: 81|9,54,54,63
657: 81|9,9,9,9,54,54
659: 830|9,9,9,54,54
661: 861|9,9,27,54
663: 863|9,9,9,54
```

## Search changes and first results

**COMPUTED.** Initial schedule `[2,3,3,2,2,3,5,7]` first-slice probes: 24 BUDGET at 45 s. A short `[2,3]` escalation used 300 s/configuration, 2M nodes, 100M lifts, modulus cap 10^18 and depth 80. Thirteen completed results were checkpointed (all BUDGET); the batch then stopped on a pending SIGALRM during timer teardown. The local harness now catches that teardown race. No incomplete certificate was written.

The old generator filtered primes from the both-unbounded (`uu`) list whenever `<3,7>` had index 1. Such primes still provide the valid ordinary `prime` kill when X/2^t0 == 0 mod p. `optimize.py` retains the small primes of that kind (p <= 10000), caches arithmetic only on the generator side, and reuses the unchanged adic signature when the refinement factor does not change its period. `generator_selfcheck.json` records a 12,696-lift comparison against the unoptimized generator signature and replay of every removed lift using the original prime test. Neither checker nor any builtin is monkeypatched.

**COMPUTED.** `supply_search.py` independently sieves primes through 3,000,000, retains short decimal periods or nontrivial `<3,7>` index, and partially factors selected cyclotomic values. It merges the original B and existing C caches, adding 442 newly searched primes, for 2,199 total. The original final modulus 15120 aligns no newly added prime; new periods are available for alternate schedules. The cache is only a search aid: checkers recompute primes and orders.

Four one-slice configurations yielded complete unordered certificates with the original rich schedule and the improved generator: `37|54,54,72`, `556|9,27,54`, `676|9,18,45`, `716|9,54,72`. Each passed both direct checkers in the first replay (8 PASS verdicts); final hashes and replays are recorded separately. No new kill type was introduced.

The assigned configuration `161|18,18,54,63` contains the previously known member 33718272. A future complete certificate is allowed to list that member at an exact-size leaf; closure means a complete member list rather than nonexistence.

**COMPUTED.** The 300-second original-rich-schedule escalation closed `133|18,18,54,54` (K=1196) in 253.873 s, 36,028,745 attempted lifts and about 169,110 nodes. The other eleven selected dimension-5 configurations reached wall-time limits. All 175 dimension-6/7/8 configurations were checkpointed BUDGET because the next flat factor-7 level needs more than 100M lifts (hundreds of millions through hundreds of billions, by dimension).

A per-class richness trial with factor-5 whole-class probing completed sixteen 60-second BUDGET results and was then interrupted at a checkpoint: diagnostics showed repeated expensive factor-5 probes before the intended small-factor richness steps. The next variant removes factor 5 from the opportunistic probe list while retaining the eventual forced factor-5 alignment. A separate two-configuration 600 s / 300M-lift run explores the flat-rich schedule without its final global factor-5 step.

**COMPUTED.** Removing the final flat factor-5 level was productive: the 600-second / 300M-lift first-slice probes completed `112|18,54,54,63` in 266.062 s and `103|45,45,54,54` in 388.976 s. Both are one-slice configurations, so these are complete covers awaiting direct checker replay and final promotion. The checkers are invoked on the unchanged original `verification/highdim/codex/checkhd.py` and `verification/v14_checknd_hd.py`, with `-I -B`; `-B` prevents bytecode writes outside this continuation's directory.

For future continuation, a bounded 24-configuration batch (at most two 600-second waves with twelve workers) is:

```sh
timeout 1700 bash -c 'ulimit -v 6000000; python3 -I verification/highdim/codex3b/continue.py next_no5_600 --seconds 600 --nodes 2000000 --lifts 300000000 --mcap 1000000000000000000000000 --depth 120 --schedule old_no5 --factors 2,3,5 --maxdim 5 --workers 12 --limit 24'
```

This is a reproduction suggestion, not an additional executed run. Repeating that stage selects its next unattempted keys; completed covers are reused. A new stage name is needed to retry previously budget-limited keys with new parameters. Every newly emitted certificate must still receive both direct checker PASS verdicts before being counted as proved.

## Completed broad pass and prime-period comparison

**COMPUTED.** The 152-configuration adaptivecheap60 pass finished with every attempted configuration BUDGET. Together with the earlier 175 higher-dimensional attempts and the closed cases, every one of the 332 assigned keys received an attempt in this continuation. `merge_results.py` retains the strongest completed configuration attempt and references to every checkpointed stage.

The period-17 comparison emits no certificates and makes no additional proof claim. Both S37 supply variants exceeded the next-level 100M-lift cap. The extended supply for S676 hit its 60-second search alarm. The S676 B-only control did not return a checkpoint before the external 300-second process limit terminated the comparison batch; it is explicitly BUDGET. In the extended S676 search, newly available primes 103, 613, 4013, 210631, 2071723 and 21993833369 actually produced successful generator tests; their counts are in `period17_results.json`. This establishes search activity, not an independently checked cover.

**PROVED, checked.** All seven retained certificate files passed both original checkers directly: 14 PASS verdicts, zero failures/timeouts in the final checker ledger. Independent E slicing gives a complete cover and every far-digit ordering for each of the seven configurations. Each is the initial qmin=3 domain, so no finite exceptional placement is left by these closures; the earlier <=600 sweep is only hashed for context. No new actual member was found in these closed configurations. The configuration containing 33718272 remains BUDGET.

## Final checked handoff

# Codex3b final research report

**PROVED (checked certificate covers), COMPUTED (counts).**
Assigned: 332 configurations of t=14112; closed: 7; still open/BUDGET: 325.
7 ordinary nd certificates passed both checkers directly: 14 PASS verdicts. No new kill type and no checker changes.

Every closed configuration has an independently replayed E slice cover and complete far-digit ordering coverage. All generated certificates, including any partial configuration slices, were checked. Each closed configuration is covered from its original qmin=3 domain, so no finite exceptional placement is left. The prior E lattice enumeration through 600 digits is hashed for context and was not rerun.

Closed keys:
- `103|45,45,54,54`
- `112|18,54,54,63`
- `133|18,18,54,54`
- `37|54,54,72`
- `556|9,27,54`
- `676|9,18,45`
- `716|9,54,72`

Files:
- `summary.json`: exact closed/open lists.
- `share.json` and `baseline.json`: exact original assignment and source hash.
- `results_t14112.json`, `stage_*.json`, and logs: checkpointed attempts and diagnostics.
- `certs/t14112/`: complete certificate trees only.
- `checker_results.json`, `logs/checks/`: direct checker commands, hashes, verdicts and timings.
- `coverage_summary.json`, `independent_coverage.json`: slice/domain/order audit.
- `supply_search.json`, `supply_extended.json`, `period_strengths.json`: prime supply work.
- `manifest.json`: hashes.

All remaining configurations are BUDGET; no nonexistence claim follows. No files outside codex3b and notes/highdim_codex3b.md were written by this continuation. No git commit was made.
