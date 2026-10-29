# Preserved limitations and corrections

Root reported default-parallel MeanFiniteCertificate compilation hitting 3 GiB;
root's -j1 replay passed unchanged sources. This packet requires -j1 everywhere.

Own initial 35 mathematical modules passed serially. The first combined audit
with an unnecessary `import Lean` reached sampled 3,242,569,728 bytes and was
killed; a first per-origin Centered audit with that import reached 3,223,007,232
bytes and was killed. No limit was raised. The correction is per-origin audits
without `import Lean`; required metaprogramming APIs are already imported by the
mathematical modules. Mathematical proof bytes were never changed. Initial logs
and replay are retained adjacent to the archive, not passed off as a full PASS.

The first PDF build caught a 24.57745pt overfull equation. Splitting its displayed
line fixed it; final build asserts absence of Overfull and is visually reviewed.
A deliberate 94-only derivative mutation is rejected by the exact checker; that
negative control is expected and not a failed proof.

Strongest surviving objection: a prior global ratio theorem or a fully verified
routine classical specialization could subsume the whole source outcome. Existing
bounded reviews found none. Missing MathDB access and incomplete specialist-body
coverage persist. Final current registry/prior-art reconciliation and independent
packet/manuscript review belong to root. Credit remains zero.
