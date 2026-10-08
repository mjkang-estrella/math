I've finished reading all three files; here is the review.

# H005 inverse walk: independent cost and evidence review (source only, no execution)

**Verdict: conditionally accepted.** I found no correctness or hidden-advice problem in the source. There is one item the root must decide on paper before the single capped run (item 1). There are also four small accounting or reporting fixes, and none of them changes the verdict.

I read the files only. Nothing was run, imported, or computed numerically. The event counts below are hand counts taken from the source.

Hashes reviewed (`sha256sum`):
- `inverse_walk.py`: `968c1886389556eda86478f3c2f26a6741b2b908053dde5e182456f3173f1731`
- `inverse_walk_protocol.md`: `5d1e5eedbcb0269439618ef7d7ada3ebda574e7f6c92b70448c0f5ed6c516a01`
- `research/findings/H005-inverse-walk-preflight.md`: `cfd09c21a21765d84442cda6a79e106c9cba43b562ce081244b825cdd603b6a6` (the file is under `research/findings/`, not top-level `findings/`)

## Where the source matches the protocol
- **Gauss reduction** (`inverse_walk.py:329-346`): it stops when `aa >= 2|D|`, including equality. The nearest-integer quotient rounds ties toward zero and takes D's sign. It uses only integers, no floats and no cache. The score `(0,)` for O and `(1, h, x, y)` otherwise matches the I1 definition (proposal lines 15-16), so O always ranks lowest.
- **Attempt loop** (`:369-424`): each state checks O, then −G, then the dictionary, then the timeout at t=T. The order holds at t=0 and at t=T. The halving is the real `[37]R` double-and-add followed by one addition. The coefficient updates and the three recovery formulas are correct. A zero denominator ends the attempt as a failure. Every claimed answer is checked with `verify`, and a false answer raises, gets caught as an error, and gives exit 2. The dictionary is rebuilt for each attempt. The only state shared across attempts is the paid setup (H, −H, −G, inv2).
- **Expectation** (`:476-542`): it computes `[setup·s + ΣC(r) + 2^b, s]` per category, which equals setup + ΣC/s + (2^b/q)/u with u=s/q. That is correct by Wald's identity for i.i.d. restarts with replacement, and C(r) is deterministic. b=7 and 2^b=128. The sampler charges match the protocol: one comparison and one loop event per raw draw, and one unbiased bit, left shift, OR and loop event per bit. The output says no real draws were executed. If s=0 the result is infinite. Timeouts and zero-denominator failures are included.
- **BSGS reference** (`:432-473`): 7 baby steps, step = 13G, giant indices i=0..6, covering [−6, 84], which spans all of Z/73. The x-key, sign recovery and identity sentinel are correct. Running out of giants raises an error. It uses the same `Field`/`Curve` code as the candidate.
- **Hidden advice:** I found none. Admission results never reach either solver, the solvers see no table indexed by scalar or log, and the restart enumeration is not passed in as advice.
- **Phase accounting:** every `before` snapshot is taken at the right point. The driver's single loop tick is kept out of the attempt vectors and recorded under its own phase. If an attempt is cut off, its events appear only in `partial_phase_event_vector` and no expectation is computed for an incomplete domain. Reconciliation compares the full category vector, and a mismatch forces exit 2.

## Item for the root to decide before the run (not a source bug)
1. **The 1,000,000-event cap does not guarantee the run completes.** Rough hand counts from the source:
   - field inversion ≈ 65 events
   - generic affine addition ≈ 87, doubling ≈ 96
   - `[37]R` ≈ 700
   - one transition with two scores ≈ 950
   - per-attempt overhead (`[r]G` plus the add, and the verify `[k]G` on success) ≈ 1.4k
   - admission ≈ 3k, BSGS ≈ 2k

   **Worst case is about 73 × (1.4k + 18 × 0.95k) ≈ 1.35M events, which is over the cap.** The run finishes only if attempts average about 12 or fewer transitions. A random-map birthday estimate gives roughly 9 (about 0.75M events), which is not a guaranteed margin.

   The protocol allows no warmup and no cap reset, and an incomplete domain gets no verdict. So hitting the cap would use up the single run without a result. The root should accept that risk explicitly in writing now, or amend the cap through review before the run. Raising it afterwards would be a post-hoc budget change. These are estimates, not measurements.

## Minor fixes (none blocks the run)
2. **Restart loop is not charged to the solver.** The outer loop costs one event per attempt, and that event goes only to the diagnostic driver. The solver expectation therefore leaves out q/s loop events (≤73/s). Either add one loop event per attempt to the solver numerator or state the exclusion. The `verified` comparison already serves as a charged success check.
3. **An expectation can appear in a failed run.** If BSGS fails or the cap is hit after `exact_expectation`, the output still contains `candidate_expected_work` while the status is `incomplete`. Label it as not admissible for the gate, or drop it, so nobody quotes it.
4. **The fixed-Q comparison is uneven between the two solvers.** Restarting from `R=Q+[r]G` spreads the start over the whole group. Apart from the cost of verifying `[k]G`, the candidate's law is therefore effectively independent of k, so it is close to an average over uniform secrets. BSGS's cost at this Q is a single k-specific value, fixed by `giant_index` (from 1 to 7 giants). The gate report must state this. A "survive" result can come from an unluckily late BSGS index, and a "lose" result can come from an early one.
5. **Pre-stated limits on a "park" outcome.** If the candidate is parked, that verdict covers only this frozen implementation. That means halving by direct `[37]R` double-and-add, a fresh `[r]G` for each restart, Fermat-exponent inversion, and a reference that is not the strongest known (no simultaneous inversion and no paired ±/x-only arithmetic in the walk). It does not rule out cheaper halving, correlated restarts or other timeouts, which matches the protocol's own scope. A "survive" result supports nothing beyond proposing a new reviewed protocol, because the reference is weaker than the best known one.

## Still open (outside this review)
- Peak memory is reported per attempt and is not aggregated across attempts or with BSGS's 7 records. That is acceptable because memory is reported separately, never added to work.
- The independent native reviewer is still checking mathematical correctness of the Gauss reduction's shortest-vector argument and of the I1 tie convention.

No improvement claim follows from this source in any outcome.
