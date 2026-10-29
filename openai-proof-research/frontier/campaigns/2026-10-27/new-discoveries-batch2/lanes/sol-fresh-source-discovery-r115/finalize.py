import json,hashlib,re,time,os
from pathlib import Path
lane=Path(__file__).resolve().parent
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(65536),b''):h.update(b)
 return h.hexdigest()
utc=lambda:time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())
cats={k:0 for k in ['SUMMARY','discovery','PROOF','FINDINGS','review','ledger','SCREENED-OUT','tools/scripts/agent/openproblem','copied_review_actual_math']}
n=size=hits=0
late_echoes=0
for line in (lane/'audit-manifest.jsonl').open():
 r=json.loads(line);assert re.fullmatch('[0-9a-f]{64}',r['sha256']);assert r['bytes']>=0
 n+=1;size+=r['bytes'];hits+=r['bounded_hits'];p=r['path']
 # Historical search inventories can have nonstandard names. Their text is
 # not mathematical evidence; preserve only a reclassification receipt.
 if ('history' in Path(p).name.lower() and p.endswith('.json')) or '/private/history/' in p:
  late_echoes+=1
  with (lane/'late-echo-reclassification.jsonl').open('a') as ef:ef.write(json.dumps({'path':p,'sha256':r['sha256'],'bytes':r['bytes'],'reason':'historical transcript/inventory echo; technically hashed/searched, excluded from mathematical-source evidence'})+'\n')
 for k in cats:
  if (k=='copied_review_actual_math' and ('review' in p.lower()) and any(t in p for t in ['/fresh/','/extracted/','/evidence/','/reproduction/'])) or (k!='copied_review_actual_math' and k.lower() in p.lower()):cats[k]+=1
exc=exbytes=0
for line in (lane/'audit-exclusions.jsonl').open():
 r=json.loads(line);exc+=1;exbytes+=r.get('bytes',0)
last=json.loads(list((lane/'audit-continuations.jsonl').open())[-1]);assert last['traversal_complete']
coverage={'status':'completed original-text traversal; streamed metadata syntax/hash-field validation PASS','utc':utc(),'files':n,'bytes_hashed':size,'bounded_recorded_hits':hits,'categories':cats,'excluded_generated_echo_records':exc,'excluded_generated_echo_bytes':exbytes,'scope':'all dates beneath openai-proof-research; .md/.txt/.tex/.py/.lean/.json/.jsonl/.html/.bib/.csv/.tsv; own lane and .git/.lake/node_modules/__pycache__ excluded','limits':['Binary PDF-only bodies without a retained text version are not semantically searched by this text audit.','Live concurrent workspace: hashes record bytes at scan time, not an immutable global snapshot.','No worldwide or current-registry absence follows.'],'initial_error_corrections':['CPU limit preserved; resumed from metadata, never rehashed completed segment.','Initial ID hit-loop omission corrected by native exact-ID pass over all335778 originals.','Initial buffered semantic hit records were lost on CPU kill; native semantic supplement scans original paths again, without rehashing or corpus copies.'],'corpus_policy':'Only per-file path/hash metadata and bounded relevant match records. Existing generated corpora excluded by explicit basename patterns; never copied or read as mathematical sources.'}
coverage['late_reclassified_history_echoes']=late_echoes
coverage['limits'].append('Some historical search/transcript echo JSON had nonstandard names and was technically scanned before recognition. late-echo-reclassification.jsonl excludes it as mathematical evidence; no substantive inference rests on it. The335778 count is technical records, including this late-reclassified subset.')
(lane/'audit-coverage.json').write_text(json.dumps(coverage,indent=2)+'\n')
sources=[]
for name,url in [('transversal.pdf','https://d-nb.info/1346963460/34'),('transversal.txt','https://d-nb.info/1346963460/34')]:
 p=lane/'sources'/name
 sources.append({'path':str(p.relative_to(lane)),'url':url,'sha256':digest(p),'bytes':p.stat().st_size,'retained_at_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime(p.stat().st_mtime)),'time_note':'filesystem completion timestamp; initial curl request-start time not separately captured','format':'published PDF' if name.endswith('.pdf') else 'local pdftotext derivative; not independent source'})
sources+=json.loads((lane/'source-fetch-receipts.json').read_text())
provenance={'utc':utc(),'lane':str(lane),'status':'full ordinary refutation candidate; source/math self-PASS; independent substantive review pending; public novelty HOLD; credit0','source':{'authors':['Stefanos Aivazidis','Maria Loukaki','Thomas W. Müller'],'title':'On the common transversal probability','doi':'10.1515/jgth-2024-0030','publication':'Journal of Group Theory27(2024)1233–1285','problem':'5.6','page':1281,'preprint_id':'2209.00986','preprint_v1_utc':'2022-09-02T12:25:19Z','preprint_v2_utc':'2023-05-31T09:45:16Z','quantifiers':'For every two finite lists of distinct integers>1, equality of products Gamma(t+1)/t^t is proposed to force equal lengths and equal entries after rearrangement. Witness is disjoint across both lists, so meets either reading of distinctness.','closest_read_bodies':['source Theorem4.6 complete proof pp1263–1265: one side distinct primes','source Proposition3.2 complete counting proof','source Proposition3.14 and Theorem3.15 proofs','Aivazidis–Loukaki–Sambale author manuscript TheoremA proof and Lemma3.1; neighboring complement existence scope']},'retained_sources':sources,'registry':{'latest_inherited_omega':'89cda9c274d1122b7676173296af3047c3b64cd1','inherited_omega_utc':'2026-10-29T20:10:57Z','latest_inherited_openai':'7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a','pinned_catalogue':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','status':'HOLD; no new HEAD/tree API request or reset inference','limits':['old HEAD/tree403 unclosed','old300-file compare cap unclosed','baseline18:13 complete inventories plus bounded chains are inherited, not current clearance']},'public_search':{'queries':['On the common transversal probability conjecture solution','Aivazidis 5.6 factorial','common transversal probability 5.2','common transversal probability 5.6','common transversal probability 5.8','factorial multiplicatively independent n^n','exact witness','2209.00986 conjecture solved'],'scope':'bounded web search plus actual primary bodies; no absence guarantee; search tool did not provide per-query UTC, so none invented'},'access_limits':['Public HTTP200 bodies retained; no blocked registry API retry or alternate endpoint bypass.','No accounts/browser tabs/contact/posting/upload.','No worldwide historical priority clearance.'],'ordinary_proof':'PROOF.md','checks':'verify_exact.py / exact-results.json; exact rational, integer and prime valuations','audit':'audit-coverage.json','strongest_objection':'An earlier public distinct-product collision or directly subsuming theorem would exclude credit; standard integer kernel permits repetitions and alone does not furnish distinct supports.'}
(lane/'provenance.json').write_text(json.dumps(provenance,indent=2,ensure_ascii=False)+'\n')
# Stream own packet manifest. The manifest and its verification receipt do not hash themselves.
skip={'manifest.jsonl','manifest-verification.json','finalize-run.log'}
with (lane/'manifest.jsonl').open('w') as f:
 for base,dirs,files in os.walk(lane):
  dirs[:]=[d for d in dirs if d!='__pycache__']
  for name in files:
   if name in skip:continue
   p=Path(base,name);f.write(json.dumps({'path':str(p.relative_to(lane)),'bytes':p.stat().st_size,'sha256':digest(p)})+'\n')
count=0
for line in (lane/'manifest.jsonl').open():
 r=json.loads(line);p=lane/r['path'];assert digest(p)==r['sha256'] and p.stat().st_size==r['bytes'];count+=1
(lane/'manifest-verification.json').write_text(json.dumps({'status':'PASS','files':count,'manifest_sha256':digest(lane/'manifest.jsonl'),'utc':utc(),'method':'streamed full rehash of every own-packet manifest entry'},indent=2)+'\n')
print(json.dumps({'coverage':coverage,'own_manifest_files':count}))
