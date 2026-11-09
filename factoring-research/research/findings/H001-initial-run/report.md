# Bounded experiment report

Descriptive measurements only. No polynomial-time or novelty conclusion.
Each trial is one (instance, algorithm seed); repeats are not independent instances.
Event medians use successes only and are selection-biased if any trial failed.
`event_budget`, `timeout`, `wave_budget`, and `no_factor` remain in denominators.

| Family | bits | Algorithm | Success/trials | Status counts | Median success events |
|---|---:|---|---:|---|---:|
| balanced | 12 | fermat | 2/2 | success:2 | 9.0 |
| balanced | 12 | rho | 2/2 | success:2 | 83.0 |
| balanced | 12 | trial | 2/2 | success:2 | 43.0 |
| balanced | 16 | fermat | 2/2 | success:2 | 14.0 |
| balanced | 16 | rho | 2/2 | success:2 | 83.0 |
| balanced | 16 | trial | 2/2 | success:2 | 197.0 |
| balanced | 20 | fermat | 2/2 | success:2 | 19.0 |
| balanced | 20 | rho | 2/2 | success:2 | 143.5 |
| balanced | 20 | trial | 2/2 | success:2 | 883.0 |
| balanced | 24 | fermat | 2/2 | success:2 | 164.0 |
| balanced | 24 | rho | 2/2 | success:2 | 358.0 |
| balanced | 24 | trial | 2/2 | success:2 | 2953.0 |
| close | 12 | fermat | 2/2 | success:2 | 9.0 |
| close | 12 | rho | 2/2 | success:2 | 39.0 |
| close | 12 | trial | 2/2 | success:2 | 47.0 |
| close | 16 | fermat | 2/2 | success:2 | 9.0 |
| close | 16 | rho | 2/2 | success:2 | 83.0 |
| close | 16 | trial | 2/2 | success:2 | 227.0 |
| close | 20 | fermat | 2/2 | success:2 | 9.0 |
| close | 20 | rho | 2/2 | success:2 | 278.0 |
| close | 20 | trial | 2/2 | success:2 | 751.0 |
| close | 24 | fermat | 2/2 | success:2 | 9.0 |
| close | 24 | rho | 2/2 | success:2 | 369.0 |
| close | 24 | trial | 2/2 | success:2 | 3527.0 |
| control | 0 | fermat | 0/2 | no_factor:2 | — |
| control | 0 | rho | 0/2 | no_factor:2 | — |
| control | 0 | trial | 0/2 | no_factor:2 | — |
| control | 1 | fermat | 0/2 | no_factor:2 | — |
| control | 1 | rho | 0/2 | no_factor:2 | — |
| control | 1 | trial | 0/2 | no_factor:2 | — |
| control | 2 | fermat | 0/4 | no_factor:4 | — |
| control | 2 | rho | 0/4 | no_factor:4 | — |
| control | 2 | trial | 0/4 | no_factor:4 | — |
| control | 3 | fermat | 2/2 | success:2 | 1.0 |
| control | 3 | rho | 2/2 | success:2 | 1.0 |
| control | 3 | trial | 2/2 | success:2 | 1.0 |
| control | 4 | fermat | 2/2 | success:2 | 1.0 |
| control | 4 | rho | 2/2 | success:2 | 1.0 |
| control | 4 | trial | 2/2 | success:2 | 1.0 |
| control | 5 | fermat | 2/2 | success:2 | 9.0 |
| control | 5 | rho | 2/2 | success:2 | 17.0 |
| control | 5 | trial | 2/2 | success:2 | 3.0 |
| control | 7 | fermat | 0/2 | no_factor:2 | — |
| control | 7 | rho | 0/2 | event_budget:2 | — |
| control | 7 | trial | 0/2 | no_factor:2 | — |
| control | 10 | fermat | 2/2 | success:2 | 14.0 |
| control | 10 | rho | 2/2 | success:2 | 17.0 |
| control | 10 | trial | 2/2 | success:2 | 3.0 |
| control | 11 | fermat | 2/2 | success:2 | 44.0 |
| control | 11 | rho | 2/2 | success:2 | 17.0 |
| control | 11 | trial | 2/2 | success:2 | 5.0 |
| square | 12 | fermat | 2/2 | success:2 | 8.0 |
| square | 12 | rho | 2/2 | success:2 | 66.5 |
| square | 12 | trial | 2/2 | success:2 | 47.0 |
| square | 16 | fermat | 2/2 | success:2 | 8.0 |
| square | 16 | rho | 2/2 | success:2 | 327.5 |
| square | 16 | trial | 2/2 | success:2 | 229.0 |
| square | 20 | fermat | 2/2 | success:2 | 8.0 |
| square | 20 | rho | 2/2 | success:2 | 531.0 |
| square | 20 | trial | 2/2 | success:2 | 797.0 |
| square | 24 | fermat | 2/2 | success:2 | 8.0 |
| square | 24 | rho | 2/2 | success:2 | 743.0 |
| square | 24 | trial | 2/2 | success:2 | 3919.0 |
| unbalanced | 12 | fermat | 2/2 | success:2 | 2714.0 |
| unbalanced | 12 | rho | 2/2 | success:2 | 22.5 |
| unbalanced | 12 | trial | 2/2 | success:2 | 3.0 |
| unbalanced | 16 | fermat | 2/2 | success:2 | 13364.0 |
| unbalanced | 16 | rho | 2/2 | success:2 | 55.5 |
| unbalanced | 16 | trial | 2/2 | success:2 | 11.0 |
| unbalanced | 20 | fermat | 0/2 | event_budget:2 | — |
| unbalanced | 20 | rho | 2/2 | success:2 | 28.0 |
| unbalanced | 20 | trial | 2/2 | success:2 | 3.0 |
| unbalanced | 24 | fermat | 0/2 | event_budget:2 | — |
| unbalanced | 24 | rho | 2/2 | success:2 | 22.5 |
| unbalanced | 24 | trial | 2/2 | success:2 | 5.0 |

Composite trials: 126; successes: 122.
Prime/0/1 controls are outside the composite-input contract; failure on these is not a factoring counterexample.

Next: review the hypothesis's preregistered falsifier and inspect results.jsonl.
Record rejected, revised, promising, or inconclusive in a finding; update research/STATE.md.
A passed screen still needs unseen instances, matched baselines, and proofs.
