from pathlib import Path
import resource,signal,json,hashlib,shutil
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(230)
L=Path(__file__).resolve().parent
assert (L/'dev/AllCases.olean').exists()
runs=[json.loads(s) for s in (L/'runs.jsonl').read_text().splitlines()];(L/'measurements.json').write_text(json.dumps(runs,indent=2)+'\n');shutil.copy2(L/'runs.jsonl',L/'runs-development.jsonl')
inp=L/'inputs/source-only-component.zip';h=hashlib.sha256(inp.read_bytes()).hexdigest();assert h=='2c5aae27c888458cfcc5f7de0ffff5bcf4c6d65efa4d151035c8a411adcd7cc8'
provenance=dict(credit=0,additional=5,total=35,acceptance_owner='root',input_archive_sha256=h,development_completed_cases=70,remaining_geometric_cases=0,FiniteCases_closed=True,unconditional_UniversalContainer=True,source_refutation=True,final_fresh_replay='receipt delivered separately; do not infer fresh success from development completion',independent_enumeration_lane='not read or polled',network='none',writes='assigned lane only',groups='every selected group separately kernel-checked as member of original literal groups; a subset suffices by FiniteBridge.excludes',table_restriction='selected group mask with every full row at least12, then all rows and inequalities re-certified in Lean; no Python completeness premise',mask_coverage='encode/decode inverses, recursive submask membership, ordered coverage and symmetry theorem',resources=dict(python_AS_MiB=512,Lean_group_RSS_MiB=2800,sample_seconds=.045,Lean_wall_seconds=230,CPU_seconds=210,threads=1,BLAS_threads=1),failures=[r for r in runs if r['rc']!=0])
(L/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
(L/'SUMMARY.md').write_text('''# All geometric cases integrated; fresh replay receipt delivered separately

Credit 0. Counts remain 5 additional / 35 total. Root owns acceptance and manuscript.

All 33 residual geometric cases compile in development, with the 37 immutable completed cases reused unchanged. `AllCases.finiteCases` is unconditional `FiniteCases`; `AllCases.universalContainer` is unconditional `UniversalContainer 11 witness`; `AllCases.source_refutation` proves `¬ SourceFormula`. These names are in `Polyomino57.Diagonal.FiniteProof.AllCases`. The fresh extracted replay and actual types/axioms/origins/safety audit are mandatory; consult the separately delivered receipt for their result.

The first new entire case was `(10,8,1)`, including domain equality, point injection, original-group membership, packed bounds/base/edge/all-union merge/full checks and FiniteBridge.excludes. The same construction then closed every table case. Selected smaller group families are legitimate original constraints, not altered group semantics: every member is proved to be in the literal original family. Each restricted table is fully re-certified; Python selection supplies data only.

MaskBridge proves binary membership, both encoding inverses, union/intersection/disjoint-complement identities, table row correspondence, and recursive submask coverage. unionCheck_sound covers all ordered disjoint nonempty pairs; PackedHalf.halfCheck_sound proves the symmetry reduction. Bound checks run once per row and are reused. Base, actual adjacency, packed merge and full-row checks are separate. All slices are joined by a proved List take/drop identity; an external expected count is never a logical premise.

The three forced cases use exact 11-cell completions of the forced vertices. Every completion is covered by powersetCard proofs. Each has a literal disconnected cut or misses an original group. `(8,4,0)` does not assert all completions are disconnected; its three connected completions miss a group. Its coverage proof is split structurally over the actual free-cell set.

The original unsplit adjacency and later base checks exceeded the RSS cap. Separately certified adjacency lists and finite mask batches resolved these failures. The initial monolithic forced coverage check also exceeded RSS; powersetCard insertion identities and smaller checks resolved it. Diagnostics and all resource measurements are retained. A generator initially used ordinary coordinates for singleton centers, whereas the formal centers use signed-diagonal coordinates; the kernel rejected those statements and the generator was corrected. One check failed from a wrong working directory without writing outside this lane; one coverage build saw newly added helper imports before their compilation and was rerun in dependency order. No mathematical source was written outside this lane. No other live lane or independent enumeration worker was inspected.

The source-only packet contains exactly the consumed formal closure, the immutable input archive, scripts, provenance, measurements and failure logs. Development reused candidate oleans. The final extracted replay consumes no candidate oleans. Only the inherited attachCheck partial helper exception is permitted; the safety audit rejects all other new partial/unsafe/axiom declarations. No sorry, admit, new axiom, native_decide or evaluator axiom is used. No claim of novelty or acceptance is made.
''')
(L/'INTERFACE.md').write_text('''All endpoint names below are in Polyomino57.Diagonal.FiniteProof.AllCases.

- remaining : RemainingCases
- finiteCases : FiniteCases
- universalContainer : UniversalContainer 11 witness
- eligible : EligibleSize 11 57
- minimum_le : minimumSize 11 ≤ 57
- source_refutation : ¬ SourceFormula

No residual hypothesis occurs in these endpoints. Witness and source semantics are the frozen definitions. The source formula predicts58 at11, while the witness has57 vertices.

New generic representation interfaces are in Polyomino57.Diagonal.FiniteProof.Packed: encode, encode_bit, encode_lt, decode, decode_encode, encode_decode, encode_union, encode_and, encode_nonzero, encode_disjoint, encode_complement, rowOf, rowOf_decode, submasks, encode_mem_submasks, unionCheck_sound, row_bounds, all_split, halfCheck, bitCheck_comm, halfCheck_sound. Frozen Packed.bits_certificate and FiniteProof.excludes are reused unchanged. Actual instantiated types and axioms are printed in the fresh FinalAudit log and parsed inventory; audit success is reported separately.

Per-case C... and R... namespaces expose certificate, original literal domain/group checks and case_a_b_e. F740, F830, F840 expose the three forced geometric cases. The packet module manifest is the consumed dependency closure, not every development attempt.
''')
