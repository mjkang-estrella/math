from pathlib import Path
import json,hashlib,datetime
P=Path(__file__).resolve().parent
fs=json.loads((P/'frozen-inputs.json').read_text());checks=[]
for f,h in fs.items():
 p=Path(f);actual=hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None
 checks.append({'path':f,'expected':h,'actual':actual,'match':actual==h})
(P/'frozen-after.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'count':len(checks),'mismatches':[x for x in checks if not x['match']],'checks':checks},indent=2))
receipts=[{'file':str(f),**json.loads(f.read_text())} for f in sorted(P.glob('*.receipt.json'))]
(P/'receipts.json').write_text(json.dumps(receipts,indent=2))
# Structured audit records successful invocation completion, not an invented sampled RSS measurement.
(P/'execution-audit.json').write_text(json.dumps({'execution_scope':'source fetch, text extraction, source-tree/history screening, hashing and five-page PDF rendering only','heavy_DP':False,'Lean':False,'children':False,'jobs_finished':True,'fetch_concurrency_max':2,'CPU_seconds_limit_per_process':120,'wall_seconds_limit_per_invocation':140,'address_space_limit_GiB':6,'RSS_sampled':False,'resource_limit_caveat':'Address-space cap is conservative relative to RSS; no claim of sampled peak RSS or cumulative multi-invocation CPU120s','processes_left_running':[],'errors':['Initial broad rg output truncated; switched to explicit inputs','Initial two reconnaissance Python commands omitted -I -B','pdftoppm scale argument initially int; corrected to string and reran successfully','ABM guessed PII wrong and returned403; correct journal body remains unread','Secondary pdfft returned403; no retries']},indent=2))
manifest={str(f.relative_to(P)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(P.rglob('*')) if f.is_file() and f.name not in ['SHA256SUMS','artifact-hashes.json']}
(P/'artifact-hashes.json').write_text(json.dumps(manifest,indent=2));(P/'SHA256SUMS').write_text(''.join(h+'  '+n+'\n' for n,h in manifest.items()))
print('frozen',len(checks),'mismatches',sum(not x['match'] for x in checks),'artifacts',len(manifest),'receipts',len(receipts))
