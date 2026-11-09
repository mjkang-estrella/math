# Round 5 validation

The strict serial replay and fresh extracted replay are recorded in
replay-report.json and verification/replay-report.json. Each module is compiled
with warnings as errors, then checked by leanchecker naming that module.
Audit5 includes opaque bodies and generated declarations, and compares the
entire inventory with the audited set in both directions, separately checking
the endpoint import closure. LOCAL and upstream metadata are reported separately.
LOCAL declarations reject unsafe/partial/axiom/_unsafe_rec/implemented_by/extern
metadata and transitive axioms outside propext, Classical.choice and Quot.sound.
The four inherited negative controls must fail. Development failures in logs
are retained as failures, not used as certificates.

All 31 frozen modules match both the original source packet and the recorded
before/after hashes. This validates partial conditional theorems only; it does
not establish the missing OrdinaryBorderTransitivity or accept the conjecture.

The first fresh replay hit the wall watchdog at Audit after completing its
inventory checks; that exit-137 run is not counted as successful. Resume logs
are retained. CPU affinity was moved from the contended pair 0,1 to 30,31;
the allowed two-CPU count and all memory/time limits were unchanged.
