# Review failures and limits

The first independent audit reader confirmed the full 35,654 declaration/type/
safety/axiom coverage and 436 origins, then rejected its own arithmetic-name
count. Its prefix predicate also counted generated declarations beneath the
1,329 theorem names. Exact full-name matching fixes this reporting predicate;
all generated declarations remain included in the exhaustive audit. The failed
reader and console are retained as verify_replay-attempt01.py and
verify-replay.console. No Lean source or audit output changed.

The initial binding helper used recursive archive discovery and encountered the
predecessor archive after successfully binding/copying the assigned top-level
archive. Its assertion correctly failed because the predecessor has a different
hash. Nothing was extracted from the predecessor in that call. Later operations
use the exact top-level path. This failure's traceback is in the task transcript.

The first inherited-source comparison selected all generated predecessor files,
including def_axiom_0.lean, which is not reused by this candidate. It failed with
FileNotFoundError. The corrected scope is the four source modules and precisely
the generated th_lemma modules containing the 1,329 reused implications.

The review source scanner initially rejected autoImplicit=false as if it disabled
checking. This was an overly broad review regex, corrected to check the actual
warning/kernel/trust options and metaprogram hooks. The next inventory check
rejected the historical Dag168 inventory module label: those 45 declarations
actually belong to parts.Dag168_000 through _044. The local scanner now permits
only this documented split, while checking every declaration and residual binder.
The final successful scans are structural-review.json and semantic-review.json.
Earlier diagnostics and exact initial inline scripts remain in the transcript;
not all intermediate scanner source versions were saved separately.

A bounded reference lookup did not find z3-proof.sexpr at the inherited DAG
directory. No scientific claim was inferred from that absence. The exact proof
hash and its prior independent parser/checker audit remain inherited evidence;
the theorem's Lean proof requires no parser/solver correctness assumption.

Upstream failed formal attempts and resource-limit failures remain in the
candidate's frozen FAILURES.md and VERIFICATION-NOTES.md; they are not successful
proofs and were not replayed as such. Review helpers retain 512MiB AS/group RSS,
CPU210/wall230; dedicated serial Lean invocations retain -j1 -M2700,
2800MiB sampled group RSS, CPU210/wall230. Sampling cannot exclude transient peaks.

No fresh network search or present registry clearance is claimed. Inherited
denials and inaccessible historical intervals remain parked. Prior review's
unread historical bodies and four citing bodies remain unread here. No worldwide
novelty, acceptance, count, manuscript, or full Conjecture17 clearance follows.
