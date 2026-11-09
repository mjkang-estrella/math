from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
admin={}
for name in ['ledger.json','prior-campaign-context.json']:
 p=L/'administrative'/name;d=json.loads(p.read_text());admin[name]={'snapshot_sha256':H(p),'accepted':[(x.get('number'),x.get('title'),x.get('scope')) for x in d['accepted']]}
print('ADMINISTRATIVE',json.dumps(admin,ensure_ascii=False))
(L/'administrative-reading.json').write_text(json.dumps(admin,indent=2,ensure_ascii=False))
checks=[]
for r in json.loads((L/'freeze.json').read_text()):
 checks.append({'original':r['original'],'original_unchanged':H(Path(r['original']))==r['sha256'],'copy_unchanged':H(Path(r['copy']))==r['sha256']})
prov={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_freeze':'freeze.json','retrieval_receipts':'retrieval.jsonl','primary_body_bindings':['text-bindings.json','scout-text-bindings.json','grabner-binding.json','last-bindings.json'],'original_copy_recheck':checks,'historical_direct_references':len(json.loads((L/'history-references.json').read_text())),'history_scope':'direct SUMMARY/SCOUTING/discovery under campaign lane roots; generated nested copies excluded; no exhaustive history clearance','registry':'No current head. Forbidden GitHub routes not retried. No novelty clearance.','administrative':'snapshots only','caps':{'AS_bytes':536870912,'sampled_groupRSS_bytes':536870912,'CPU_seconds':210,'wall_seconds':230},'failures':['unrelated200 publisher page','unrelated Bing RSS','initial quadratic/in-place coding manually terminated without result','initial expanded history root error corrected before use'],'credit':0}
(L/'provenance.json').write_text(json.dumps(prov,indent=2))
manifest={str(p.relative_to(L)):{'sha256':H(p),'size':p.stat().st_size} for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['final-manifest.json','verification-receipt.json']}
(L/'final-manifest.json').write_text(json.dumps(manifest,indent=2))
print('MANIFEST',len(manifest),'files; original/copy',all(x['original_unchanged'] and x['copy_unchanged'] for x in checks))
