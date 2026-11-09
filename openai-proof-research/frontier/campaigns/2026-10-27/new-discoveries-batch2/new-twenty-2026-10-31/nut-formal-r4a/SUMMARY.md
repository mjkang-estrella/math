# MathDB 365943 — r4a Part A

The exact requested theorem is proved in `formal/EndpointOfFinite.lean`:

```lean
Nut8.endpoint_of_finite (h : Nut8.FiniteObstruction) : Nut8.Target
```

There are no additional hypotheses. `Target`, `FiniteObstruction`, `Admissible`, `SupportConnected`, `unsignedQuotient`, `Nut`, and all inherited modules are unchanged byte for byte. The result is conditional only on Part B, which belongs to the separate r3b lane. This lane does not prove FiniteObstruction, claim an unconditional inhabitant of Target, self-accept, or change campaign credit. Root acceptance remains required; the count stays 20/40 beyond 39.

`coordinate_signedQuotient_admissible` derives the frozen grammar for exactly `signedQuotient m (coordinateGraph G L) ε`, with `s = ε^(m/2)`. The proof transports cubic degree through L, identifies absolute entries with actual neighbor fiber cardinalities using the inherited character-coherence theorem, sums the partition into fibers, and transfers the original nut cut property to support cuts. A symmetric matrix with absolute row sums three and connected support on eight vertices has entries of magnitude at most two: a triple entry saturates both endpoint rows and isolates at most two vertices. This also excludes a diagonal magnitude three.

For the diagonal, a zero neighbor count gives zero, a two-neighbor count gives ±2 by coherence, and a singleton shift b must equal -b by translation invariance and graph symmetry. Looplessness gives b ≠ 0, and the representative identity m - b.val = b.val gives b.val = m/2. The shared diagonal contribution is therefore ε^(m/2). This handles the diagonal grammar without assuming a separate loop classification theorem. Explicit small-orbit lemmas give zero diagonal for m = 1 and either zero or ε for m = 2.

The endpoint uses the same quotient extraction as r3a. Its quotient kernel vector v is lifted back by `characterLift`; periodicity and the inherited lift identity prove a full actual graph kernel vector with the required character formula. The grammar bridge and `integer_full_kernel_det_adjugate` then contradict the assumed FiniteObstruction on the same matrix.

New source modules: AdmissibleCounting, AdmissibleDiagonal, EndpointOfFinite, SmallOrbitCases, and R4Audit. All input files were hashed before copying; required copies have identical hashes. The r3a packet matches its prescribed SHA-256. Final validation and declaration counts are recorded in results.json and replay-receipts.json.

No child agents, git operations, external retrievals, shared ledger edits, or other-lane writes were used. All output, temporary files, logs and extracted builds are inside this lane. Every Lean/checker call runs serially under the supplied two-CPU, 6 GiB private-RSS, 120-second CPU and 140-second wall watchdog with MALLOC_ARENA_MAX=2.
