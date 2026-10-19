# r108: T104AS unresolved

No eligible full candidate closed. No nomination, independent PASS, campaign
acceptance, publication, or count increment is claimed. Intake remains18/20;
the parent owns integration and all independent gates.

The unchanged [frozen target](scope.md) asks for a uniform deterministic
`2^{O(log^2 L)}` algorithm computing every almost-sure winning state for
stochastic **liminf mean-payoff >=0 AND parity**, with arbitrary binary
weights/probabilities/priorities and arbitrary behavioral opponents.

[Working proof report](working.md) gives technical support: a gain/bias
martingale prefix certificate, a qualitative deletion reduction for ordinary
mean payoff, and an even-priority combination lemma under an explicit lower
strategy certificate. It also proves an all-rational-parameter obstruction
to replacing the deterministic recursion's attractors by positive stochastic
attractors. None of these support results is nominated separately.

The remaining steps are a stochastic boundary/dominion invariant with
extraction and quasipolynomial halving accounting, and closure of the global
liminf prefix-certificate induction. The primary priority-dependent recursion
and a terminal redirection proposal do not supply those steps.

[Inventory](inventory.md) records five distinct operation-level screens and
their historical comparisons. [Reading limits](reading-limits.md) and the
JSON receipts state actual reading extents, pinned paths/blobs/SHA256 and the
failed primary retrieval. No claim of exhaustive literature priority is made.

`diagnostics.py` is a small exact-arithmetic control program. Its saved JSON
checks interior rational absorption examples, zero-probability endpoints,
and a mixed-sign potential fixture. These finite checks support, but do not
prove, the general arguments in the report. Replay without writes:

```
python3 -B diagnostics.py
```

`manifest.json` seals exact packet membership, including private local
evidence. Its detached SHA256 is supplied in the handoff, not inferred from
an untrusted neighboring file. From this directory, verify read-only with:

```
python3 -B verify.py --expected-manifest-sha256 <detached-SHA256>
```

The verifier needs the existing repository's complete tree and upstream
pointer. It treats changes to the live ledger/other historical context as
reported drift, not silent permission to reseal. Do not distribute private
third-party bodies. No package for publication was made. Retrieval scripts
are historical author tools and must not be rerun over this sealed packet.

All writes for this task stayed inside the assigned r108 directory. No
shared index, other agent file, commit, staging operation, nested delegation,
browser UI, upload, PR, or external message was used. Runtime configuration
was checked as GPT-6 Astra/high/serviceTier=default. This is an author
research archive, not an independent review.
