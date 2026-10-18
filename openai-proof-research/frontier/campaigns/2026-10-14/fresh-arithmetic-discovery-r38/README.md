# T205M author proof packet

The current result submitted for independent gates is the exact frozen theorem
in `scope205m.md`. Read `candidate205m.md`, its included
`kostka-low-capacity-proof.md` and `provenance/parent-high-capacity.md`, then
`source-and-credit.md` and `reading-limits.md`. This is not an accepted result
or a campaign count increment. Campaign status at submission:14/20.

The initial checkpoint, pre-freeze exploratory report and intermediate
`inherited-recursion-work.md` are historical and superseded in status.
They are preserved to keep the scope chronology honest. The original scope
bytes and all other sealed project packets remain unchanged.

From any copied packet directory, run:

```bash
PYTHONDONTWRITEBYTECODE=1 python verify-finite-proof.py
PYTHONDONTWRITEBYTECODE=1 python finite-crosscheck.py
python verify.py EXTERNALLY_SUPPLIED_MANIFEST_SHA256
python control-tests.py EXTERNALLY_SUPPLIED_MANIFEST_SHA256
```

The first command exactly recomputes the finite proof certificate, including
all required bases and the m7,8 induction boundary. The second independently
checks cell-grid versus bead strips/characters through degree10. These finite
steps do not prove the universal symbolic lemmas by testing.

The last two commands authenticate exact file and directory inventory and
exercise13 canonical/copied/adversarial controls, including wrong external
anchor, self-reseal, symlinks, hardlinks and FIFO. The verifier never reseals.
Pass the manifest digest received outside this packet; do not trust a newly
computed replacement digest as the authorization anchor. Control output should
be captured outside the sealed packet, or left on stdout. Its temporary copies
are removed before the command returns. Integrity checks do not certify proof
correctness, source truth or substantiality.

Private third-party bodies and canonical context copies are in ignored
`private/`. They are part of local identity verification and must not be
committed or released. A public-only copy is not the same complete local
inventory and will intentionally fail this local verifier. Parent owns any
later release packaging, independent proof/contribution/formal/manuscript
gates and publication decision. No uploads are authorized or performed here.

Author Myeongjin Kang, no affiliation. Original prose CC BY4, original codeMIT.
