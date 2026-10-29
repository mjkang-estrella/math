from pathlib import Path
import hashlib,json,datetime
p=Path(__file__).resolve().parent;b=p.parent.parent
hashof=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
f=p/'inputs/r100-freeze.json';j=json.loads(f.read_text());src=Path(j['source_lane']);rows=[]
for name,h in j['files'].items():
 a=hashof(src/name);c=hashof(p/'inputs/r100'/name);assert a==h==c,name
 rows.append({'path':name,'original_sha256':a,'copy_sha256':c})
assert hashof(b/'lanes/root-fresh-source-r100-r101-handbacks/r100-freeze.json')==hashof(f)
guard=b/'lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py';assert hashof(guard)=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
(p/'freeze-after.json').write_text(json.dumps({'verified':len(rows),'all_unchanged':True,'guard_sha256':hashof(guard),'files':rows},indent=2))
# Integrate independently observed registry advancement, retaining supplied snapshot.
r=p/'review.md';text=r.read_text();needle='The earlier capped historical segment is incomplete.'
addition='My subsequent live HEAD receipt is Omega **73a5033dd654a16a14fcd1b13277f1a03d81d826** (committer date 2026-10-29T19:55:36Z), beyond the supplied r101 snapshot. The pinned compare from 556e to 73a5 reports **21 commits / 9 changed files**, all listed in `delta.log`; none is the Matveeva body. I retrieved the Blueprint and Lean endpoint again at that immutable new head: both hashes are identical to the copies already read. This is an incremental bounded check, not an exhaustive new semantic search. OpenAI independently remains **7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a** in my live HEAD receipt. '
assert needle in text;r.write_text(text.replace(needle,addition+needle))
sourcehashes=[]
for folder in [p/'inputs/r100/sources',p/'live',p/'context']:
 for x in sorted(folder.rglob('*')):
  if x.is_file():sourcehashes.append({'file':str(x.relative_to(p)),'sha256':hashof(x),'bytes':x.stat().st_size})
(p/'sourcehashes.json').write_text(json.dumps(sourcehashes,indent=2))
prov={'reviewer':'sol-matveeva-classical-proof-review-r1','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'role':'solo independent review; no children','candidate_proof_sha256':j['files']['PROOF.md'],'freeze_entries_verified_before_and_after':len(rows),'originals_unchanged':True,'own_byte_copies_only':True,'guard':{'path':str(guard),'sha256':hashof(guard),'AS_MiB':512,'group_RSS_MiB':512,'CPU_seconds':210,'wall_seconds':230,'nominal_poll_ms':40,'BLAS_threads':1},'helpers':['freeze.py','live.py','checker.py','context.py','delta.py','finalize.py'],'evidence':'evidence.json','exact_check_count':json.loads((p/'evidence.json').read_text())['count'],'finite_checks_validate_imported_deep_theorems':False,'source_hashes':'sourcehashes.json','context_hashes':'context-hashes.json','network_receipts':['live-http.json','delta-http.json','live/omega-head-receipt.json','live/openai-head-receipt.json'],'current_heads':{'omega':'73a5033dd654a16a14fcd1b13277f1a03d81d826','openai':'7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a'},'registry_limits':'21-commit/9-file incremental refresh; relevant two bodies unchanged; earlier capped history incomplete; no global absence claim','gates':{'source_full_scope':'PASS','ordinary_mathematics':'PASS with normalized-H/Laurent wording corrections','imported_hypotheses':'PASS','substantive':'recommend EXCLUSION: explicit complete classical bridge in review.md','historical_novelty':'HOLD; bounded only','formal_endpoint':'not supplied or compiled','paper_and_extraction':'not supplied or run','acceptance':'root only'},'credit':0,'counts':{'additional':8,'total':38},'review_sha256':hashof(r),'prohibited_actions_performed':False,'shared_edits':False,'git':False,'children':False,'external_messages':False,'browser_preview':False,'lean_or_paper':False}
(p/'provenance.json').write_text(json.dumps(prov,indent=2))
manifest=[]
for x in sorted(p.rglob('*')):
 if x.is_file() and x.name not in ['artifact-manifest.sha256','finalize.log','finalize.guard.json']:manifest.append(hashof(x)+'  '+str(x.relative_to(p)))
(p/'artifact-manifest.sha256').write_text('\n'.join(manifest)+'\n')
print(json.dumps({'status':'PASS','originals_verified':len(rows),'exact_checks':prov['exact_check_count'],'report':str(r),'artifacts_hashed':len(manifest)}))
