from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).parent
(R/'provenance.json').write_text(json.dumps({'retained_metadata_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_freeze':'bindings.json','source_acquisition':'sources.json recorded before pdftotext','search_results':'search metadata only; no primary-proof reliance','evidence_cap':'5 PDFs, selected50 statements; no corpus copies; flat original refs','resource_guard':'../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py','limits':'512MiB AS/groupRSS CPU210s wall230s; no raises'},indent=2)+'\n')
files=[]
for p in sorted(R.rglob('*')):
 if p.is_file() and p.name not in {'manifest.json','verification-receipt.json'}:files.append({'path':str(p.relative_to(R)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size})
(R/'manifest.json').write_text(json.dumps({'files':files},indent=2)+'\n')
print(len(files),'files manifested')
