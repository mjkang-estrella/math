import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(210,210))
import json,hashlib,datetime,re
from pathlib import Path
R=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
receipt=json.loads((R/'verification-fresh/replay-receipt.json').read_text())
assert receipt['status']=='COMPONENT_REPLAY_PASS_SOURCE_INCOMPLETE'
assert receipt['declaration_count']==89
assert len(re.findall(r"^'.*' (?:depends on axioms:|does not depend on any axioms)", (R/'verification-fresh/logs/AuditPrint.log').read_text(),re.M))==89
assert not re.search(r'\b(sorryAx|Lean\.ofReduceBool)\b',(R/'verification-fresh/logs/AuditPrint.log').read_text())
inputs={str(p.relative_to(R)):sha(p) for p in (R/'inputs').rglob('*') if p.is_file()}
(R/'provenance.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'INCOMPLETE; component replay only; credit0; counts7/37 unchanged','inputs':inputs,'source_url':'https://link.springer.com/chapter/10.1007/978-981-95-7127-7_24','source_pdf_sha256':sha(R/'inputs/live/publisher.pdf'),'source_location':'printed356, physical4; exact unequal-degree sign visually read from copied publisher-page356.png; extraction loses negation stroke','freeze_before':sha(R/'freeze-before.json'),'freeze_after':sha(R/'freeze-after.json'),'archive_sha256':sha(R/'edge-irregulator-component.zip'),'new_remote_reads':False,'external_actions':False,'math_modules':['Source','Boundary','Gadget','Edges','Degrees'],'unique_declarations':89,'audit_modules':['OriginAudit','AuditPrint'],'failed_probes_preserved':'probes/; includes all failed Lean sources/logs/receipts and helper failures','resource_deviations':'No RSS/CPU/wall/Lean memory cap was raised or triggered. package-01 attempted to reset an inherited hard AS limit to infinity and was rejected before work; preserved. Corrected helper uses hard AS512. Replay helper AS512 soft/hard-infinity to permit explicitly approved Lean AS-infinity in a separate guarded process group. Python itself retains AS512.','audit_exception':'AuditPrint alone disables linter.auxLemma to enumerate unstable auxiliary names intentionally. No mathematical-module linter disabled.','scope':'No source refutation theorem, global lower/upper deletion theorem or transport supplied.'},indent=2)+'\n')
print('FINAL: component only, 89 declarations, 89 literal #print axioms, allowed axioms only; source incomplete')
print('archive',sha(R/'edge-irregulator-component.zip'))
print('max replay RSS KiB',max(s['peak_group_rss_kib'] for s in receipt['steps']))
