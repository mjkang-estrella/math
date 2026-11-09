from research import *
import importlib.util,stat
spec=importlib.util.spec_from_file_location('v',OUT/'packet/public/verify_packet.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
for name in ['MANIFEST.json','outsideREPORT.md','FINAL.json','ANCHORS.json']:
 assert not (OUT/name).exists(),'seal once: envelope already exists'
entries=v.inventory(OUT)
m={'format':'r141-exact-root-v1','created_utc':now(),'root_mode':stat.S_IMODE(OUT.stat().st_mode),'entries':entries}
(OUT/'MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n');mh=sha((OUT/'MANIFEST.json').read_bytes())
nf=sum(e['type']=='file' for e in entries);nd=len(entries)-nf
report=f'''# Outside report — structural discovery r141

PREFREEZE / no nominee. The precise derivations, read/search/chronology/rights limits and parent handoff are in packet/public/handoff.md and packet/public/prefreeze-derivation.md. No scope was frozen. No independent correctness, contribution, acceptance, count or downstream stage is claimed.

The sustained calculation gives an exact common-polymatroid-base representation of distinct retained-coordinate vectors, using hidden-pair slack, a restricted submodular minimum and integral decomposition. It preserves binary capacity complexity and removes completion multiplicities. Its strongest compatible inputs are already paid source/classical operations; it is not submitted as a nonroutine full finding. The preceding fractional-power route is also covered by the actual coefficient-power closure. The elementary-unimodality screen overlapped prior authored targets and was not resumed. Old targets and dispositions remain unchanged.

The payload has {len(entries)} exact entries: {nf} files and {nd} directories, including work scripts and one miniature copied-control fixture. The manifest excludes only the four top-level envelope files named in the verifier. Nested fixture envelopes are sealed as ordinary payload. Detached MANIFEST SHA256: {mh}

The complete nontruncated tree has 13223 entries and SHA256 eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b. Thirty-six pinned raw source blobs were reauthenticated by tree path, size, Git blob and SHA256. Acquisition and inventory do not imply semantic reads. Four external PDF/text pairs have version/URL/hash receipts; read extents and failed original Edmonds acquisitions are explicit. The supplied T205 anchors matched, without any upstream truth or author-correctness audit.

Finite arithmetic checks covered eight small inputs and 68 visible-coordinate choices in feasible cases. The copied artifact fixture had nine expected rejection cases, baseline success and restored success, with no writes by the verifier. These are not mathematical gates. The read-only verifier must be run after sealing with the three external SHA256 anchors; ANCHORS.json is not an independent authority.

Seventeen named immutable originals and all eighteen stored baseline copies matched their recorded bytes. The mutable NEW-TEN ledger changed between observations and is separately recorded; it was not written by this lane. This is not a historical whole-parent or whole-project preservation claim. Other-lane routing is mutable observation, not a premise.

The initial filename-pruning error, partial/truncated displays, coarse corpus exclusions and late reads are disclosed. The new analytic-r135 and arithmetic-r105 patterns applied only prospectively from their recorded policy update; subsequent traversal pruned them before descent. No active lane or in-progress review body was used as a premise. All new writes stayed inside r141. No git action, nested agent, publication, upload, submission, contact, browser UI or downstream stage was performed. Parent alone integrates/reviews/counts. Publication remains stopped.
'''
(OUT/'outsideREPORT.md').write_text(report);rh=sha((OUT/'outsideREPORT.md').read_bytes())
f={'format':'r141-final-v1','sealed_utc':now(),'status':'PREFREEZE_NO_NOMINEE','scope_frozen':False,'author_proof_nominee':False,'manifest_sha256':mh,'outside_report_sha256':rh,'pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','tree_sha256':'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b','payload_files':nf,'payload_directories':nd,'payload_entries':len(entries),'assigned_provenance':'Codex / GPT-6 Astra / high / default service tier','mathematical_disposition_authority':'parent only; no self gates','count_change_requested':False,'publication':'STOPPED','preservation':'17 named immutable originals matched; 1 mutable campaign ledger changed and separately recorded; all 18 baseline copies matched; no whole-parent historical claim','limits':'packet/public/read-and-scope-limits.md','handoff':'packet/public/handoff.md'}
(OUT/'FINAL.json').write_text(json.dumps(f,indent=2)+'\n')
a={'MANIFEST.json':mh,'outsideREPORT.md':rh,'FINAL.json':sha((OUT/'FINAL.json').read_bytes())};(OUT/'ANCHORS.json').write_text(json.dumps(a,indent=2)+'\n')
print(json.dumps(a,indent=2));print(nf,'files',nd,'directories')
