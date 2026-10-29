from pathlib import Path
import hashlib,json,datetime,re
L=Path(__file__).parent;R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
def digest(p):
 h=hashlib.sha256();n=0
 with p.open('rb') as f:
  while b:=f.read(1048576):h.update(b);n+=len(b)
 return {'sha256':h.hexdigest(),'bytes':n}
http=[]
for name in ['http.jsonl','more-http.jsonl','bodies-http.jsonl']:
 with (L/name).open() as f:
  for line in f:http.append(json.loads(line))
counts={x:0 for x in ['2409.12404','2503.22377','2402.00949','2605.09609','Houshan','Filipi','Kubjas']}
with (L/'duplicate-triage.jsonl').open('w') as out:
 for name in ['required-hits.jsonl','supplement-hits.jsonl']:
  with (L/name).open() as f:
   for line in f:
    row=json.loads(line);t=row['text']
    for term in counts:
     for m in re.finditer(re.escape(term),t,re.I):
      counts[term]+=1;out.write(json.dumps({'inventory':name,'path':row['path'],'term':term,'excerpt':t[max(0,m.start()-160):m.end()+250]})+'\n')
refs={}
for rel in ['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','frontier/campaigns/2026-10-27/new-discoveries-batch2/AGENTS.md','frontier/campaigns/2026-10-27/new-discoveries-batch2/ledger.json','frontier/campaigns/2026-10-27/new-discoveries-batch2/NEXT.md','frontier/campaigns/2026-10-27/new-discoveries-batch2/prior-campaign-context.json','frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/root-edge-irregulator-final-freeze-r1/CURRENT-REGISTRIES.json','frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-fresh-source-discovery-r108/provenance.json','frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-fresh-source-discovery-r108/refresh-http.json','frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:
 refs[rel]=digest(R/rel)
pro={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lane':str(L),'status':'NO ELIGIBLE DISCOVERY; Hayashi unresolved; Fu routine classical specialization; neural public refutation','credit':0,'source_receipts':http,'local_context_references':refs,'duplicate_term_counts':counts,'duplicate_limits':'Counts over streamed required plus supplemental hits, with overlap; no same Fu/Hayashi source ID/author occurrence found. Not semantic absence; nonmatching authors with Hayashi surname are unrelated. All-date scans include copied review trees and embedded Markdown screening notes. Broad initial audit CPU210 failure retained.','registry':{'baseline_utc':'2026-10-29T18:13:38.748036+00:00','omega_latest_successful_head':'89cda9c274d1122b7676173296af3047c3b64cd1','head_timestamp':'2026-10-29T20:10:57Z','openai_head':'7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a','status':'INHERITED HOLD: aggregate300 comparison cap and subsequent403; no fresh API request, no reset assumed; not semantic clearance'},'access_errors':['guessed Zaslavsky paths404; author-index true links subsequently successful','Zaslavsky PDF pdftotext empty; tesseract missing, native visual read replaces OCR','initial broad audit reached sampled groupCPU210s; retained partial streams','initial regex omitted arXiv version suffix; corrected audit2 and supplement positive/negative tests PASS'],'no_lean':True,'no_paper':True,'no_children_git_shared_writes_external_messages':True,'guard':'Unchanged referenced helper_guard.py;512MiB AS/sampled groupRSS,210CPU,230wall,40ms nominal,BLAS1','manifest_scope':'All lane payload except manifest itself, finalize/verify output logs and guard receipts (circular/later-created). JSONL inventory/content files retained including incomplete broad pass. Sources retained as received.','verification':'Consult verify.log and verify.guard.json; this field does not predict execution.'}
(L/'provenance.json').write_text(json.dumps(pro,indent=2)+'\n')
skip={'manifest.jsonl','finalize.log','finalize.guard.json','verify.log','verify.guard.json'}
with (L/'manifest.jsonl').open('w') as out:
 for p in sorted(L.rglob('*')):
  if not p.is_file() or p.name in skip:continue
  row={'path':str(p.relative_to(L)),**digest(p)};s=json.dumps(row);out.write(s+'\n');out.flush();print(s,flush=True)
