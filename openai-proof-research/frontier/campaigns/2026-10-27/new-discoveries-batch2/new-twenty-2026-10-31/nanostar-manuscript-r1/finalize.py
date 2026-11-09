from pathlib import Path
import json,hashlib,shutil,datetime,zipfile,subprocess
B=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/nanostar-manuscript-r1');P=B.parent
h=lambda p:hashlib.file_digest(open(p,'rb'),'sha256').hexdigest()
def save(path,v): (B/path).write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
before=json.loads((B/'inputs-before.json').read_text());after={rel:{'sha256':h(P/rel),'bytes':(P/rel).stat().st_size} for rel in before};save('inputs-after.json',after)
assert before==after
assert all(h(B/'frozen'/rel)==v['sha256'] for rel,v in before.items())
save('receipts/input-integrity.json',{'status':'PASS','original_files':len(before),'before_after_equal':True,'frozen_copies_equal':True,'utc':now})
parent={}
for name in ['replay-result.json','registry-refresh.json']:
 f=P/'nanostar-parent-final-r1'/name
 if f.exists():
  prior=h(f);data=f.read_bytes();assert prior==hashlib.sha256(data).hexdigest()==h(f)
  target=B/'frozen/nanostar-parent-final-r1'/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
  parent[name]={'status':'present','sha256':prior,'contents':json.loads(data)}
 else:parent[name]={'status':'pending','reason':'Named final receipt absent at packaging'}
save('receipts/parent-final-status.json',{'utc':now,'receipts':parent})
raw=B/'frozen/expanded-corpus-r162/raw/349177.jsonl';entry=json.loads((B/'mathdb-entry.json').read_text());assert h(raw)==entry['provenance']['raw_sha256']
save('receipts/raw-record.json',{'path':str(raw.relative_to(B)),'sha256':h(raw),'bytes':raw.stat().st_size,'matches_input_provenance':True,'line_count':len(raw.read_bytes().splitlines())})
pages=sorted((B/'qa').glob('page-*.png'));assert len(pages)==6
save('receipts/page-qa.json',{'status':'PASS','PDF_sha256':h(B/'paper.pdf'),'pages':6,'inspection':'All six final PNGs opened and visually inspected by the manuscript agent. Text, table columns and rows, page numbers, bibliography and footers legible; no overlaps, clipping, missing glyphs or spill pages observed.','images':[{'path':str(x.relative_to(B)),'sha256':h(x)} for x in pages],'utc':now})
r=json.loads((B/'recomputation.json').read_text());assert r['status']=='PASS'
issues=['Published title adds "the" before Euler compared with preprint and brief short title.','Conjecture occurs on printed p. 271, not the bibliography page 272.','Contraction is an interpretive source bridge, not an explicit source definition.','Review HOLD on four compiler-generated partial helpers was resolved by the root ruling; no helper is reported reachable from the endpoint.','D2 maximum 334 in the discovery control and 564 in the source control refer to different witnesses; no numerical conflict.']
result={'mathdb_id':349177,'title':'An 88-vertex totient realization of the four-stage contracted nanostar','status':'DRAFT; packaged for root review, not accepted','AI_assistance':'OpenAI Codex','human_authors':[],'pages':6,'recomputation':'PASS','witness':{k:r['D4'][k] for k in ['generators','order','edges','centre','layers','maximum_label']},'D2':{k:r['D2'][k] for k in ['order','edges','centre','maximum_label']},'D3':{k:r['D3'][k] for k in ['order','edges','centre','maximum_label']},'arithmetic_discrepancies':[],'input_qualifications':issues,'formal_endpoint':'R162.not_conjecture349177 : ¬ R162.Conjecture349177','formal_replay_this_task':False,'proof_packet_sha256':h(B/'proof-source.zip'),'safe_extraction':'PASS','input_integrity':'PASS','page_QA':'PASS','root_final_receipts':parent,'accepted_credit':0,'campaign_context':'41/60 beyond 39; root alone accepts','literature_limits':['Tau-function successor DOI 10.1063/5.0315935 full text unread','Rashid et al. 2020 full text unread','Bounded registry/title/statement screens do not certify worldwide novelty'],'artifacts':{'paper':'paper.pdf','source':'build_paper.py','prose_source':'paper.md','proof':'PROOF.md','reproduce':'REPRODUCE.md','dossier':'full-dossier.zip','lean_packet':'proof-source.zip'}}
save('results.json',result)
statuses='; '.join(name+': '+v['status'] for name,v in parent.items())
(B/'SUMMARY.md').write_text('''# An 88-vertex totient realization of the four-stage contracted nanostar

DRAFT, AI-assisted (OpenAI Codex); no human authors or affiliations asserted. Six pages. MathDB 349177. No publication or priority claim. Zero credit; root alone accepts. Campaign context: 41/60 beyond 39.

The final conjecture of Nima Ghanbari and Saeid Alikhani is false at stage 4 under the openly stated contracted-hexagon interpretation. The source never explicitly defines that contraction; its Figure 10 matches the cited Deutsch–Klavzar Figure 12.

Fresh isolated Python verification: PASS. The 23 generators give exactly 88 vertices, 87 edges, centre 1024 and layers 1,3,3,3,6,6,6,12,12,12,24. Every factorization, totient value, orbit, edge and nonedge is checked; an independent recursive tree model and explicit isomorphism agree, including every ordered pair of the actual formal certificate labels. D2 and D3 controls pass (16 and 40 vertices). No mathematical discrepancy was found.

Input qualifications: the published title adds “the” before Euler; the conjecture is on printed p. 271. Stage-2 maxima 334 and 564 come from different control witnesses. The review's literal metadata HOLD and root qualified-pass ruling are both retained: four compiler-generated partial helpers exist but are outside the reported endpoint closure. The Tau-function successor and Rashid et al. full texts remain unread. Significance is modest; routine inverse-totient backtracking found the witness.

The Lean packet is reused BYTE-IDENTICALLY, SHA-256 5aa1150cb685221b2f9dbfbab4cd9eff9f503d917add10b62a491a1e19d81fac. Its safe-extraction test passed. No Lean, lake, leanchecker, solver, network, git, browser or child agent ran in this task. Existing strict replay/audit logs are retained without claiming a fresh replay here.

Root final receipt status at packaging: '''+statuses+'''. See receipts/parent-final-status.json.

Deliverables: paper.pdf; build_paper.py (complete PDF source); paper.md; PROOF.md; REPRODUCE.md; recompute.py and recomputation.json; results.json; proof-source.zip; full-dossier.zip; manifest.json and manifest.sha256; receipts/; qa/ (all six visually inspected page PNGs); frozen/ (exact raw record, source PDFs/text and original receipts, reviews and logs). All 433 selected original frozen input hashes and their copied bytes agree before and after.
''')
save('receipts/source-copies.json',{'status':'PASS','copies':before,'policy':'Every original selected frozen input and its dossier copy has the stated SHA-256; original retrieval receipts are preserved without alteration.'})
save('receipts/final-verification.json',{'status':'PASS','mathematics':r['status'],'order_recurrence_and_branch_layers':r['order_recurrence_and_branch_layers'],'original_inputs_unchanged':True,'packet_byte_identical':True,'packet_safe_extraction':'PASS','PDF_pages':6,'all_pages_visually_inspected':True,'network_used':False,'formal_tools_run':False,'solver_run':False,'child_agents_used':False,'scope':'All new files confined to this lane; no shared ledger edits or publication. Packaging and later verification resource receipts are external to the archive snapshot.','utc':now})
# All files existing at packaging, except circular manifests/archive receipts and transient lock files.
exclude={'manifest.json','manifest.sha256','full-dossier.zip','receipts/dossier-archive.json'}
files=[x for x in sorted(B.rglob('*')) if x.is_file() and x.relative_to(B).parts[0]!='tmp' and str(x.relative_to(B)) not in exclude]
manifest={str(x.relative_to(B)):{'sha256':h(x),'bytes':x.stat().st_size} for x in files}
save('manifest.json',{'algorithm':'sha256','files':manifest,'exclusions':sorted(exclude)+['tmp/'],'purpose':'Dossier content integrity; external archive receipt binds the outer ZIP'})
(B/'manifest.sha256').write_text(''.join(v['sha256']+'  '+k+'\n' for k,v in manifest.items()))
files += [B/'manifest.json',B/'manifest.sha256']
with zipfile.ZipFile(B/'full-dossier.zip','w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for f in sorted(files):
  info=zipfile.ZipInfo(str(f.relative_to(B)),date_time=(2026,11,4,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;info.external_attr=0o100644<<16;z.writestr(info,f.read_bytes())
with zipfile.ZipFile(B/'full-dossier.zip') as z:
 assert z.testzip() is None
 for f in files:assert hashlib.sha256(z.read(str(f.relative_to(B)))).hexdigest()==h(f)
save('receipts/dossier-archive.json',{'sha256':h(B/'full-dossier.zip'),'bytes':(B/'full-dossier.zip').stat().st_size,'entries':len(files),'CRC_test':'PASS','every_member_byte_comparison':'PASS','manifest_json_sha256':h(B/'manifest.json'),'manifest_sha256_file_sha256':h(B/'manifest.sha256'),'note':'External receipt excluded from the archive to avoid circular hashing','utc':now})
print(json.dumps({'pages':6,'recomputation':r['status'],'inputs':len(before),'archive_entries':len(files),'root_final_status':{k:v['status'] for k,v in parent.items()},'dossier_bytes':(B/'full-dossier.zip').stat().st_size},indent=2))
