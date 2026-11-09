"""Run only after full_audit.py succeeds; package then freeze lane manifest."""
from pathlib import Path
import hashlib,json,subprocess,os
L=Path(__file__).resolve().parent
G=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
a=json.loads((L/'replay/full-audit-receipt.json').read_text());assert a['status']=='PASS'
(L/'VERIFICATION.md').write_text(f'''# Verification report

Fresh strict serial replay PASS for the literal endpoint
`Assembly.literal_endpoint : FloorSums.LiteralEndpoint`.
All 437 mathematical modules and 22 exhaustive audit partitions succeeded:
459 Lean invocations, 35,654 safe nonpartial declarations, 436 actual origins;
Dag168 is the sole empty import wrapper. Private/generated declarations and
instances are included. Exact type, safety and transitive-axiom name sets match.
Only propext, Classical.choice and Quot.sound occur transitively. All 59 inherited
source declarations and 1,329 arithmetic theorem names are covered.

Name-set SHA256: {a['names_sha256']}.
Maximum sampled Lean group RSS: {a['max_sampled_group_RSS']} bytes.
Maximum individual Lean wall time: {a['max_invocation_wall']:.6f} seconds.
Every invocation used the fixed binary, -j1 -M2700, CPU210/wall230 and unchanged
2800 MiB group RSS guard. Helpers used the exact required predecessor guard and
512 MiB AS/group RSS, CPU210/wall230. The incomplete local-guard attempt is
preserved separately and does not contribute to this receipt.

The replay tree is a fresh copy of the clean frozen-input extraction, with only
the documented replay-shell guard-path configuration added; it contains no
imported owned objects. The final archive extraction is byte-compared against
this replay's every mathematical file and against the original archive. The
final extraction is not described as a second independent compilation. Root's
own final extracted replay remains pending.

All nine actual package heads and the Lean executable hash match pins.json.
The trusted external built library caches are not rebuilt here. Full actual
type/safety/axiom outputs remain in replay/logs/Audit*.log. The machine-readable
full-audit-receipt.json records this lane's run, separately from r4's independent
receipt. No Lean mathematical source was edited; all 460 input Lean files,
including unused historical audit/display source, remain byte-identical.

Archive byte reproduction and source integrity are separate checks. Both ZIP
and gzip/tar are rebuilt twice with canonical metadata, extracted and checked
member-for-member. archive-receipt.json records hashes. A separate guarded
verify_final.py runs after all substantive writes and checks the exact lane
manifest, scientific original/copy bindings and every extracted mathematical
source. The manifest excludes exactly itself and verification-receipt.json.

PDF NOTAUTHORED / QA_NOTPERFORMED: mandatory marker failed within unchanged caps.
Original and supported low-memory Node attempts are preserved. No PDF creation,
rendering or visual inspection is claimed. paper.md is the manuscript source.

Source fidelity PASS applies to the separately posed uniform-m four-variable
bound, not full Conjecture 17. Prior-art clearance is bounded HOLD. No worldwide
priority, acceptance, publication or credit is claimed. Current registry bodies
and listed historical/citing bodies remain inaccessible or uncleared. No denied
route was retried. Root replay, prior adjudication, final review and acceptance
remain pending. Shared counts remain 9 additional / 39 total / next40.
''')
subprocess.run(['python3',str(G),'python3',str(L/'build_packet.py')],check=True)
ar=json.loads((L/'archive-receipt.json').read_text())
subprocess.run(['python3',str(G),'python3',str(L/'final-extracted/build_packet.py')],check=True)
for n,key in [('source-packet.tar.gz','tar_sha256'),('source-packet.zip','zip_sha256'),('rebuild.tar.gz','tar_sha256'),('rebuild.zip','zip_sha256')]:
 p=L/'final-extracted'/n;assert sha(p)==ar[key];p.unlink()
(L/'standalone-rebuild.json').write_text(json.dumps(dict(status='PASS',from_final_extracted_source=True,tar_sha256=ar['tar_sha256'],zip_sha256=ar['zip_sha256']),indent=2)+'\n')
# Preserve all logs and sources; remove only owned generated compiled objects.
removed=[]
for folder in ['replay','replay-attempt01-local-guard']:
 for p in (L/folder).rglob('*'):
  if p.is_file() and p.suffix in ['.olean','.ilean','.ir','.c','.o','.so','.pyc']:
   removed.append(str(p.relative_to(L)));p.unlink()
(L/'compiled-cleanup.json').write_text(json.dumps(dict(removed=removed,logs_and_sources_preserved=True),indent=2)+'\n')
(L/'FINAL-RESULT.md').write_text(f'''# Final result

MANUSCRIPT_SOURCE_AND_SOURCE_PACKET_COMPLETE. Literal floor bound PASS.
PDF NOTAUTHORED / QA_NOTPERFORMED (mandatory marker failed; fixed caps preserved).

Endpoint: `Assembly.literal_endpoint : FloorSums.LiteralEndpoint`.
Domain: m>0; indexed ai in [0,m-1], repeats allowed; K in [0,m-1]; actual
real floors; all 16 indexed subsets including empty; bound -3 floor(m/3).
Scope: independently posed Thanatipanonda-Wong 2018 four-variable lower bound,
not full Conjecture 17, other dimensions or extremizer assertions.

Fresh strict serial replay: PASS, 437 mathematical modules + 22 audits = 459
Lean invocations. 35,654 safe nonpartial declarations across 436 actual origins;
Dag168 wrapper empty. Every actual type/safety/transitive-axiom report covered.
Only propext, Classical.choice, Quot.sound. No new proofs or mathematical source
changes; all 460 input Lean files preserved. No owned compiled objects packaged.

## Artifacts and hashes (SHA256)

* paper.md (manuscript source): {sha(L/'paper.md')}
* source-packet.tar.gz: {ar['tar_sha256']}
* source-packet.zip: {ar['zip_sha256']}
* Input source-only.tar.gz: 17ba800adb3154f5c3929ef076c47b9d1f0adaace1576793faa4154ff19be13f
* Lean binary: e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550
* mathlib revision: d13f23b723b8a846827a245b89c10fc7d3f11612; nine actual package pins in formal/pins.json.
* Declaration-name-set: {a['names_sha256']}
* replay/full-audit-receipt.json: {sha(L/'replay/full-audit-receipt.json')}
* archive-receipt.json: {sha(L/'archive-receipt.json')}

Both archive builds are byte-identical on repetition. Every extracted member
matches; original/extracted/replayed mathematical bytes agree. The packet has
{ar['members']} members, including its internal source manifest. Scientific
bindings are in bindings.json; prior reports and failures are preserved.
Full lane final-manifest.json excludes exactly itself and verification-receipt.json.
The separate guarded verify_final.py runs after these writes; its receipt holds
the final manifest hash and exact original/copy/coverage checks without a
self-referential manifest/receipt claim.

Read VERIFICATION.md and README.md for commands and trust boundaries. Replay
requires the disclosed absolute external Lean installation, built package
libraries, exact helper guard, Linux /proc/prlimit and Python3. Historical
generation scripts retain immutable external references; this is not a bundled
toolchain or recursive copy of research history. No solver is needed for replay.

Earlier incomplete local-helper replay and both PDF marker failures are
preserved in FAILURES.md/logs. Resource caps were unchanged. RSS is sampled;
unsampled transient peaks are not ruled out. No network retrieval, denied-route
retry, git/shared/public/browser/MathDB edit, child agent or publication occurred.
Source/prior body-read scope and chronology are explicit in paper.md; inherited
review evidence is attributed. Current registry proof-body clearance and listed
older/citing bodies remain HOLD; no worldwide priority is asserted.

Root's own replay, prior adjudication, final review and acceptance remain pending.
No credit or count change: 9 additional / 39 total / next40.
''')
manifest={p.relative_to(L).as_posix():sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.relative_to(L).as_posix() not in ['final-manifest.json','verification-receipt.json']}
(L/'final-manifest.json').write_text(json.dumps(manifest,sort_keys=True,indent=2)+'\n')
print('final writes complete; run separate guarded verify_final.py')
