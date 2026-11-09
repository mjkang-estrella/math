# W011 frozen-basin diagnostic

Disposition: **REJECTED** for the preregistered window. Verified factoring improvement: **NONE**.

The exact finite-field census is an oracle diagnostic. The map coefficient was acquired from the single prescribed N-only parameter draw; hidden p,q were used only to analyze its local functional graphs. No candidate factoring runtime was measured or implemented.

One main run; total wall through worker exit: 9.446882 seconds within the registered 60-second cap unless the supervisor records a deadline. Prime setup, parameter draws, chart gcds, tables, BFS, all depths and durable journal writes are charged. Source/config were frozen before the one fixed p=5,q=7,a=2 check, which passed exact direct-orbit and all-CRT-seed checks of endpoint/stopping probabilities and map-update expectations.

Primary criterion: at least 8 of the original 16 records on each of b=13 and b=15 must be clean and have min_k (1+E)/(S_stop*sqrt(p)) <= 1/4. Chart successes do not qualify. Missing primary analysis is inconclusive.

- b=7: p=131, q=137; statuses {"chart_full_failure": 0, "chart_success": 0, "clean_completed": 16, "control_completed": 0, "failed": 0, "failed_interrupted": 0, "timed_out": 0, "unstarted": 0}; qualifying clean 0/16; best clean normalized proxy 0.9152896687770805; cubic control control_completed, best normalized proxy 2.79483014046349 at k=4.
- b=9: p=521, q=523; statuses {"chart_full_failure": 0, "chart_success": 0, "clean_completed": 16, "control_completed": 0, "failed": 0, "failed_interrupted": 0, "timed_out": 0, "unstarted": 0}; qualifying clean 0/16; best clean normalized proxy 0.6123273537424082; cubic control control_completed, best normalized proxy 3.3538405445038335 at k=4.
- b=11: p=2053, q=2063; statuses {"chart_full_failure": 0, "chart_success": 0, "clean_completed": 16, "control_completed": 0, "failed": 0, "failed_interrupted": 0, "timed_out": 0, "unstarted": 0}; qualifying clean 0/16; best clean normalized proxy 0.8142932588406214; cubic control control_completed, best normalized proxy 11.35779884913924 at k=1.
- b=13: p=8209, q=8219; statuses {"chart_full_failure": 0, "chart_success": 0, "clean_completed": 16, "control_completed": 0, "failed": 0, "failed_interrupted": 0, "timed_out": 0, "unstarted": 0}; qualifying clean 0/16; best clean normalized proxy 1.1792582723386695; cubic control control_completed, best normalized proxy 16.99669343383815 at k=2.
- b=15: p=32771, q=32779; statuses {"chart_full_failure": 0, "chart_success": 0, "clean_completed": 16, "control_completed": 0, "failed": 0, "failed_interrupted": 0, "timed_out": 0, "unstarted": 0}; qualifying clean 0/16; best clean normalized proxy 8.382450542920951; cubic control control_completed, best normalized proxy 45.261738599873965 at k=2.

All case statuses: {"chart_full_failure": 0, "chart_success": 0, "clean_completed": 80, "control_completed": 5, "failed": 0, "failed_interrupted": 0, "timed_out": 0, "unstarted": 0}. All 850 depth slots: {"completed": 850, "failed": 0, "failed_interrupted": 0, "not_applicable_chart": 0, "timed_out": 0, "unstarted": 0}. Zero-success completed depths: 0. Every case and every fixed depth is retained; no seeds or adverse basins are omitted.

The optimistic work proxy omits gcds, inversion/setup constants, random bits and bit costs. Best depth uses hidden-factor oracle histograms and is not an N-only schedule. Cubic C is one fixed-map control per pair, not Pollard rho. No fitted exponent, monotone trend, asymptotic bound, ECM/GNFS comparison or speedup claim follows. Full-gcd stopping failures and no-hit survival are included in every exact S_stop count.

The registered supply of sufficiently cheap useful basins fails in this finite window. This rejects this pilot, not every parameter of the family or factoring in general. Reopening this branch would need a new justified mechanism or theorem for N-only useful-parameter supply and hitting cost, followed by separately authorized independent validation; increasing this run or selecting favorable seeds is not part of this delivery.

The separate mathematical review is not duplicated here; this finite check does not prove identities (1)-(5), basin growth, or a complexity theorem. No shared solver, Lean, state, package, commit or publication changes. The shared check.sh was not run because it launches additional tests/builds and writes outside the assigned prefix; the user's bounded-check scope controls.

Source SHA-256: `6fb87082bd5395902f446e4f6c01c9bd37a160954cf09caf49e6663ea0044e78`.

Config SHA-256: `592c836f7641cd2beea90d1b74e358e87e84679b141e65363f334be4c81edd7f`.

Freeze manifest SHA-256: `0f1186baeb06965157b3cb5f64786ea995ae7f3fce3b5ba99fd1b7259cbc4d45`.

Delivery: `-preregistration.md`, `-execution-note.md`, `.py`, `-config.json`, `-freeze.json`, `-tiny-check.json`, `-run.json`, `-scheduled.jsonl`, `-events.jsonl` (durable raw chronology and full histograms), `-cases.jsonl` (all per-case statuses), `-depths.jsonl` (all ten depths for every case), `-supervisor.json`, `-worker.log`, `-summary.json`, this report and `-manifest.json`, plus the frozen instruction snapshots. All share the `W011-basin-screen` prefix. The manifest hashes every artifact except itself.
