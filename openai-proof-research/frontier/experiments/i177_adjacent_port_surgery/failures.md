# Preserved I177 development failures

All numbered attempts have their exact `math177.py`, `research177.py`,
and `run177.py` sources retained as `.disabled`, plus stdout, stderr,
exit code, and elapsed time. None of these stages is executed during
final replay. Empty streams are retained as zero-byte files.

1. `mandatory-attempt-01`: the certificate parser expected the report's
   compact name `61`, but the data key is `6r1`. `int("r1")` failed.
   All earlier mandatory controls had run; stdout remained empty.
   The correction reads the actual schema and does not alter a path,
   vector, minor, or mathematical assertion.
2. `mandatory-attempt-02`: the checker wrongly equated the proof's
   specifically chosen glued anchor with the exhaustive enumerator's
   first product anchor. Both are valid but can differ. The corrected
   check reconstructs the proof anchor exactly, checks its local and
   exterior members belong to the actual state, and verifies its saved
   full cycle; the exhaustive-product comparison remains separate.
   Empty stdout and assertion stderr remain. This is not a U176 repair.
3. `experiment-attempt-01`: mathematics completed, but JSON serialization
   rejected exact `Fraction` entries in the two additional anchor-kernel
   directions included in the ambient basis. Only that output field
   now serializes rationals as exact strings. The empty stdout,
   TypeError, and original sources remain.

Inherited I176 selector (`7Z` versus `71`), schema (`witnesses` versus
`extensions`), and C171 reference/pre-switch failures remain strict
external byte bindings. The parent's sufficient-versus-exhaustive partner
mistake at state 5, and the extra partners at states 9/10, remain unchanged.
The inherited I175 rankUV and mixed-coordinate errors, rejected
embedding, and I174 pre-seal parent-document transition are likewise
preserved. None is silently repaired in ancestor evidence.
