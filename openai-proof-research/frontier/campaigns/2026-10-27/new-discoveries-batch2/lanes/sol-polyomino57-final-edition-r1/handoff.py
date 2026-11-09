from pathlib import Path
import json,hashlib
L=Path('.')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
files=['polyomino57-final-edition.zip','output/pdf/polyomino57-final-edition.pdf','source/MANIFEST.json','source/source-manifest.json','source/QA.json','CONTENT-IDENTITY.json','EDIT-REPORT.json','EDIT-REPORT.diff','reproduction-final/REPRODUCTION.json','INDEPENDENT-CHECK.json','resource-receipts-snapshot.jsonl']
hashes={n:sha(Path(n)) for n in files}
receipts=[json.loads(s) for s in Path('resource-receipts-snapshot.jsonl').read_text().splitlines()]
r=dict(status='READY FOR ROOT FINAL INSPECTION; deterministic artifacts and source identity PASS; no acceptance',credit=0,root_acceptance=False,counts_owned_by_root=[6,36],new_full_Lean_replay=False,mathematical_sources=2023,mathematical_modules=2022,actual_declaration_records=5924,inventory_sha256='bb24a892d49115ba1538de2994a2452088cad156d091ed69fa960f09cb50e4c9',all_sources_and_records_unchanged=True,manuscript_mathematics_displays_authorship_unchanged=True,pages_personally_inspected=[1,2,3,4,5,6,7],PDF_byte_identical_rebuild=True,ZIP_byte_identical_rebuild=True,independent_exact_payload_check=True,manifest_payload_entries=4142,zip_entries=4143,standing_dissent_preserved=True,procedural_failures_preserved=True,partial_exception='Polyomino57.attachCheck._unsafe_rec: unsafe=false partial=true axiom=false',protocol_qualification='Historical uncapped metadata helpers/cache writes retained. This edition PDF skill Node marker could not start under AS512MiB; no successful marker or all-protocol PASS claimed. 45ms RSS sampling cannot exclude shorter transients.',resource_caps=dict(AS_MiB=512,CPU_seconds=210,wall_seconds=230,groupRSS_MiB=512,BLAS_threads=1,sampling_seconds=.045),helper_runs_recorded_before_handoff=len(receipts),max_observed_groupRSS_bytes=max(v['peak_group_rss'] for v in receipts),failed_helper_runs=[v for v in receipts if v['exit']!=0],hashes=hashes,remaining_for_root=['Inspect final seven pages','Reconcile current named registry delta at acceptance','Perform separate final acceptance/count transaction if warranted'])
Path('FINAL-RESULT.json').write_text(json.dumps(r,indent=2)+'\n')
Path('SHA256SUMS').write_text(''.join(v+'  '+n+'\n' for n,v in hashes.items()))
Path('SUMMARY.md').write_text('''# Final edition handoff

Ready for root inspection; no acceptance or credit. Counts remain root-owned at 6 additional / 36 total. The scientific paper contains no campaign tally and states that replay and independent review are completed, novelty is bounded, and acceptance is separate.

- Source-only proof ZIP: `polyomino57-final-edition.zip` (4143 entries / 4142 manifest payload entries; no prebuilt Lean objects or nested archives).
- Seven-page PDF: `output/pdf/polyomino57-final-edition.pdf`; personally inspected final renders `pages/page-1.png` through `pages/page-7.png`: no clipping, overlap or missing glyph found.
- Exact changes: `EDIT-REPORT.json` and `EDIT-REPORT.diff`; seven status/provenance manuscript paragraphs, status footer, README/provenance, QA/PDF, metadata-only verifier extension, regenerated manifest, 21 documentary evidence files plus two edition notes/identity files. All indented displays and every mathematical paragraph outside those status/provenance paragraphs are exact. Authorship unchanged.
- `CONTENT-IDENTITY.json`: all2023 Lean sources and5924 actual records unchanged. The sole compiler-helper exception remains unsafe=false partial=true axiom=false. Every original evidence file, standing dissent and procedural failure note is unaltered.
- `reproduction-final/REPRODUCTION.json` and `INDEPENDENT-CHECK.json`: extracted PDF/ZIP rebuild byte-identically; the independent ZIP writer does not use pack.py. Exact payload, manifests, source identity, all actual audit records and absence of prebuilts verified.

No new full Lean replay was run. Exact source/record identity binds this edition to the completed root and independent fresh replays, whose receipts, inventories and actual audit logs are included. Root adoption retains one-family eligibility subject to the final packet; substantive dissent remains standing. No optimum, first failure, new algorithm, absence-of-prior-art, or protocol-perfection claim is made.

All computational helpers in this edition were invoked via cap.py with AS512MiB, CPU210, wall230, BLAS1 and process-groupRSS512MiB sampled45ms; no Lean invocation and no raised caps. Node marker startup failed under this cap (including jitless); one attempted option was unsupported. Historical uncapped metadata and package-cache deviations remain disclosed. Additional local fail-closed checks (incorrect changed-paragraph expectation and prohibited evidence-directory name) and the consequent missing-ZIP reproduction failure are retained in notes and resource receipts. Sampled RSS is not a continuous maximum. No successful PDF skill marker or unqualified all-protocol PASS is claimed.

Final SHA256 hashes are in SHA256SUMS and FINAL-RESULT.json. Root still owns final page inspection, current registry delta reconciliation and any acceptance/count transaction. No shared writes, proof edits, git, children, external contact or browser work occurred.
''')
print(json.dumps(dict(zip=hashes[files[0]],pdf=hashes[files[1]],manifest=hashes[files[2]],ready=True),indent=2))
