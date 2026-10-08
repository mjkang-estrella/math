# H015 source baseline: charge reusable walk preprocessing

2026-10-08. Native Sol located and read the source; root independently read
Bernstein--Lange §§2–3 using the exact primary-PDF text extraction below.
No numerical experiment or algorithm improvement. This is the comparator for
new H015 time-memory/multi-target proposals, not a new candidate.

[Computing small discrete logarithms faster](https://cr.yp.to/dlog/cuberoot-20120919.pdf)
explicitly distinguishes target-independent walks and reusable endpoint tables
from target-dependent rho steps. Its table of M endpoints incurs setup roughly
sqrt(q*M), with online work roughly sqrt(q/M) per target under the paper's walk
assumptions and parameter choices. Failed table-building walks, popular endpoints
and target-independent jump design are already part of this baseline. The
sub-square-root online term does not make the one-time setup disappear.

Our elementary accounting consequence, not a new theorem: K full logarithms
with a shared table have principal total

    sqrt(q*M)+K*sqrt(q/M)=sqrt(q)*(sqrt(M)+K/sqrt(M)).

Ignoring lower-order/constant/memory restrictions and retaining the source's
assumptions, the balance M~K gives sqrt(q*K) scale for the batch. For K1, choosing
large M does not improve total square-root work. A new proposal must state
whether it solves all K targets, one of K, or one later target after amortized
setup; these objectives are not interchangeable. Charge table construction,
memory, all failed paths, verification and online work consistently. This formula
is neither a coordinate-aware lower bound nor a calibrated practical runtime.

## Source access and reproducibility

Root's web-tool fetch returned502, but the following primary-site read succeeded:

```
curl --fail --location --max-time 20 --silent https://cr.yp.to/dlog/cuberoot-20120919.pdf | pdftotext -layout - - | sed -n '190,365p'
```

It covers the generic-method review and the beginning of§3, including setup and
online costs. Native Sol inspected a longer190–490 range. No repo file or
experiment was created by this read. FJM2014 IACR PDF initially indexed but later
timed out; HAL access denied. Official May--Ostuzzi2024/564 PDF returned403.
Indexed snippets and bibliography entries alone are not accepted as a read of
their complete theorem hypotheses; any later successful access must be recorded.

## Successful FJM followup, superseding its access failure

Native Sol subsequently obtained the actual FJM2014 PDF and read§2 in full.
Root independently read the same section using:

```
curl --fail --location --max-time 20 --silent https://iacr.org/archive/asiacrypt2014/88730171/88730171.pdf | pdftotext -layout - - | sed -n '185,310p'
```

[Fouque--Joux--Mavromati, §2, pp.4–6](https://iacr.org/archive/asiacrypt2014/88730171/88730171.pdf)
uses a fixed number of randomized chains per original target, sorts endpoints,
and constructs a graph of recovered log relations. It distinguishes recovering
a giant component from connecting all targets, retaining logarithmic overhead
in its all-target discussion. It also discusses denser starting combinations.
Thus relation graphs and reuse cannot be claimed as new. The particular
minimum-unresolved-component-count admission rule is absent from this inspected
schedule; that is not a general novelty proof. Its probabilistic analysis is
not a success theorem for our frozen32-jump/cutoff/negation attempt. May--Ostuzzi
full-source access and broader adaptive-rule comparison remain pending.

## Successful May--Ostuzzi followup

The published PKC2025 PDF subsequently succeeded through shell curl although
web-tool access failed. Sol read the introduction and complete§§4–6, printed
pp.375–382. Root independently read the all-target corollaries, complete
Algorithm6 and Theorem4 using:

```
curl --fail --location --max-time 20 --silent https://link.springer.com/content/pdf/10.1007/978-3-031-91826-1_12.pdf | pdftotext -layout - - | sed -n '920,1080p'
```

[May--Ostuzzi, §6, pp.381–382](https://link.springer.com/content/pdf/10.1007/978-3-031-91826-1_12.pdf)
precomputes a fixed known-log endpoint table, then retries each original target
until solved. Its expected square-root batch step count is an existing result,
not our improvement. Its PRF walk uses random scalar powers per step; abstract
steps cannot be equated to one EC addition. Algorithm5 removes solved targets
in successive passes. Neither inspected algorithm uses the proposed signed
component minimum-retained-count rule. This is a narrow source distinction,
not global novelty, a practical constant comparison or a success proof for our
32-jump capped walk. Sol also inspected the introduction's per-step-cost caveat.
Source gate now has actual primary algorithms; favorable complete costs and
success evidence for the H015 candidate remain missing.

Sol's additional successful primary reads (no saved files):

```
curl --fail --location --max-time 25 --show-error --silent https://link.springer.com/content/pdf/10.1007/978-3-031-91826-1_12.pdf | pdftotext -layout - - | sed -n '90,380p'
curl --fail --location --max-time 25 --show-error --silent https://link.springer.com/content/pdf/10.1007/978-3-031-91826-1_12.pdf | pdftotext -layout - - | sed -n '510,1120p'
```
