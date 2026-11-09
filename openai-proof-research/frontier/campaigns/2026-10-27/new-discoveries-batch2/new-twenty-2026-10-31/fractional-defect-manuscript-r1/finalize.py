from pathlib import Path
import json,hashlib,zipfile,shutil,subprocess,datetime
O=Path(__file__).resolve().parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def put(n,x): (O/n).write_text(json.dumps(x,indent=2)+'\n')
shutil.copyfile(O/'work/tex/paper.pdf',O/'paper.pdf')
# Reproduce exact ordinary arithmetic, retaining old review evidence unchanged.
a=O/'replay/independent-arithmetic.py';shutil.copyfile(O/'reviews/fidelity-evidence/independent-arithmetic.py',a)
p=subprocess.run(['python3',str(a)],capture_output=True,text=True);assert p.returncode==0
put('layout-verification.json',{'pages':5,'render_tool':'pdftoppm','inspection':'Every page visually inspected after final build: legible mathematics, tables, references, page numbers; no clipping or overlap.','tex_build':'Tectonic, final run no warnings','pdf_sha256':H(O/'paper.pdf'),'render_hashes':{f'page-{i}':H(O/f'work/final-{i}.png') for i in range(1,6)},'render_images_excluded_from_dossier':True})
put('version-thesis-disposition.json',{
 'mathdb_id':335230,'status':'HOLD','credit':0,'fresh_access_attempts_this_task':0,
 'source_versions':[{'body':'arXiv:1702.01442v1','date':'2017-02-05','target':'Conjecture 2, Section 3.3, p.8'},{'body':'arXiv:1702.01442v2','date':'2019-11-07','target':'Conjecture 2, Section 3.3, p.8'},{'body':'undated author preprint','target':'Conjecture 1, Section 3.3, p.8','version_of_record_authenticated':False}],
 'journal_disposition':'No distinct journal body known here. No requirement for a hypothetical journal version is imposed. Inspected dated metadata identifies no journal reference.',
 'thesis':{'author':'Honghai Xu','title':'Generalized colorings of graphs','year':2016,'title_evidence':'Included Goddard CV dissertation listing','body_read':False,'material_gap':'Direct predecessor may contain a subsuming construction. Later retained conjecture does not clear it.','official_body_url':'https://open.clemson.edu/cgi/viewcontent.cgi?article=2651&context=all_dissertations','body_failure':'403 observed circa 2026-11-01 07:14 UTC; source http-log, no response-body hash available','landing_url':'https://open.clemson.edu/all_dissertations/1650/','landing_failure':'HTTP 403 at 2026-11-01T07:21:41.299592+00:00; review new-http-receipts','action':'No retries, alternate-route bypass, new search loop or author contact. No genuinely new independent lawful-copy lead arose.'},
 'receipt_supplement':'Original packet/source-receipts.json is preserved and predates final thesis failure. sources/http-log.json and sources/review-supplement/new-http-receipts.json supply later history.',
 'registry_scope':'Dated reused verified receipts at 4eaee87548250b2682affda7d05d947c05554bae: Nov1 05:27 UTC head, 05:55 subtree. Path screen only, no exhaustive body/current priority clearance. Inherited MathDB403/Palomar403 retained.',
 'resolution_authority':'Root literature adjudication and acceptance remain separate.'})
(O/'README.md').write_text('''# MathDB 335230 draft dossier

Draft only. Exact certified claim: D(K_2^(4),3) <= 5/3 < 2; universal source equality false. The exhibited maximum is exactly 5/3, with no claim of optimality. Literature HOLD remains material; candidate credit 0; campaign accepted 1/20 unchanged.

- paper.pdf and paper.tex: five-page ordinary manuscript, definitions, complete witness proof, known-result comparisons, formal mapping and limits.
- original/proof-packet.zip: original frozen seven-file packet, byte preserved. This is the only nested archive, explicitly requested, not recursive historical packaging.
- proof/: exact Lean, replay.py, pins, original proof/receipts/literal record.
- reviews/: selected original independent reports and complete local-declaration auditor, unchanged.
- sources/: the three primary version PDFs/texts; dated HTTP history and selected companion, slides and CV evidence.
- provenance/: corpus line plus records/provenance and dated small registry receipts. Other historical input paths in input-bindings.json are integrity/provenance pointers, not represented as bundled bodies.
- replay/: this task's fresh strict replay, all-32-declaration axiom audit, metadata revision check, lexical scan and exact rational arithmetic.
- integrity-before.json / integrity-after.json: all 33 frozen input hashes matched. These are scoped checks, not a workspace-wide unchanged assertion.

## Verify and replay

In a fresh extraction, run `python3 verify-manifest.py`, then `python3 replay-dossier.py`. The latter generates work/strict-extracted and refuses to reuse it. Linux Python3 is required. Defaults:

```
LEAN_BINARY=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean
MATHLIB_PACKAGES=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
```

Override those environment variables as appropriate. Lean 4.34.1 commit 5045d0056413266e57c625dcd7c365b10e377c52 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 are required, with the other eight packages in proof/lake-manifest.json already available as prebuilt caches. Script uses strict warnings, -j1 -M2048, two-CPU affinity, 8 GiB address cap, 90 CPU seconds soft/95 hard, 105-second wall timeout per run. AuditAll.lean contains the identical candidate followed by the auditor; no candidate edits are made. A separate arithmetic replay is `python3 replay/independent-arithmetic.py`.

Prebuilt imported oleans and exported axiom summaries are trusted external inputs. Revision metadata is checked, but source cleanliness/source-to-olean provenance and a full dependency rebuild are not established. The dossier is not fully vendored and makes no full offline rebuild claim. Original replay.py alone does not authenticate the dependency cache.

Build paper.tex using a standard LaTeX installation with amsmath, amssymb, amsthm, geometry, booktabs, array, hyperref (e.g. Tectonic). PDF bytes may vary with timestamps/tool versions. Final PDF was rendered and every page inspected; render/cache/compiled intermediates are excluded. The manifest excludes itself to avoid self-reference. The outer zip has a separate hash receipt, also outside the zip.

No author contact, external messages, publication, upload, browser tabs, git operation, ledger changes, or candidate changes were performed. Paper review, root final replay, literature adjudication and acceptance are separate gates.
''')
r=json.loads((O/'replay/replay-result.json').read_text());a=json.loads((O/'replay/declaration-audit.json').read_text())
put('results.json',{'mathdb_id':335230,'role':'research sub-agent manuscript and reproducible dossier','draft_complete':True,'overall_acceptance':'HOLD','current_credit':0,'campaign_accepted_unchanged':'1/20','claim':'D(K_2^(4),3) <= 5/3 < 2; refutes universal equality over positive m,a,k','actual_parameters':[4,2,3],'lean_indices':[3,1,2],'witness_defects':['2/3','2/3','5/3','5/3','5/3','5/3','5/3','1'],'witness_maximum':'5/3','optimum_claimed':False,'source_versions':'version-thesis-disposition.json','thesis_body_subsumption':'material HOLD; inaccessible; no new lawful independent copy lead','inherited_reviews':{'ordinary_source':'PASS','significance':'qualified PASS','fidelity':'four gates PASS under prebuilt-cache trust'},'fresh_strict_replay':{'status':'PASS','seconds':r['seconds'],'exit_code':r['exit_code'],'theorem_audits':11,'source_sha256':r['source_sha256']},'fresh_local_audit':{'status':'PASS','declarations':a['count'],'seconds':a['seconds'],'axioms':a['allowed_axioms']},'resource_limits':'-j1 -M2048, at most 2 CPUs, 8 GiB address cap, 90/95 CPU seconds, 105 wall seconds','trust':'External prebuilt cache and imported exported-axiom summaries trusted; metadata alignment only; no full dependency rebuild or source-to-olean provenance claim.','pdf':{'file':'paper.pdf','pages':5,'all_pages_rendered_and_visually_inspected':True},'input_integrity':{'before':'PASS','after':'PASS','count':33},'original_packet_unchanged':True,'candidate_unchanged':True,'not_claimed':['exact optimum','minimum counterexample size','scaling family','new formal method','worldwide priority','acceptance'],'pending_root_gates':['paper review','final replay','literature adjudication','acceptance'],'outputs':['paper.pdf','paper.tex','dossier.zip','manifest.json','SUMMARY.md','integrity-before.json','integrity-after.json']})
(O/'SUMMARY.md').write_text(f'''# MathDB 335230: draft manuscript and dossier complete

**Overall acceptance HOLD. Candidate credit 0; accepted campaign count remains 1/20.**

The five-page paper gives the exact positive-parameter source conjecture, simplex/overlap definitions, complete eight-vertex calculation and universal refutation D(K_2^(4),3) <= 5/3 < 2. It explains the separation from replicated within-part assignments and pure colorings (both best value 2), and compares the complete-graph, two-color, total-defect and divisible-part results. It claims no exact optimum, minimum-size witness, scaling family, new formal method or global priority.

Fresh safe extraction of the unchanged frozen packet: strict Lean replay **PASS**, {r['seconds']:.3f}s. Separate unchanged review auditor: **all 32 local declarations PASS**, {a['seconds']:.3f}s, only propext/Classical.choice/Quot.sound. All eleven theorem audits pass. The exact arithmetic independently reproduces the eight row sums. Nine local package revision metadata heads match the recorded pins; external imported oleans/axiom summaries remain trusted. This is not a full dependency source rebuild or source-to-olean attestation.

All 33 input bindings pass before and after. Original Lean SHA-256: {r['source_sha256']}. Original packet SHA-256: {H(O/'original/proof-packet.zip')}. The original Lean and packet bytes are unchanged. Every page of the final five-page PDF was rendered and visually inspected; final TeX compilation has no warnings.

**Version disposition:** arXiv 1702.01442v1/v2 Conjecture 2 and undated author preprint Conjecture 1 are the inspected source versions. No distinct journal body is known here, no journal requirement is invented, and the author copy is not authenticated as a version of record.

**Material thesis HOLD:** Xu 2016, Generalized colorings of graphs, is a direct predecessor. Body 403 circa 07:14 UTC and landing 403 at 07:21:41 UTC are retained. No denied route was retried or bypassed; no new search loop/contact occurred and no new independent lawful-copy lead arose. Later retention of the conjecture does not clear thesis subsumption. Original packet receipts predate the last failure and remain unchanged; outer HTTP/review receipts supplement their history.

The dossier includes source PDF versions and selected companion/slide/CV evidence, original packet, exact Lean, pins/replay, selected independent reports, later failure receipts, provenance and manifests. It excludes compiled oleans, caches, rendering/TeX intermediates and recursive historical archives. Run python3 verify-manifest.py then python3 replay-dossier.py in a fresh extraction; see README.md. The original seven-file packet is the sole nested zip by explicit request.

Root paper review, final replay, literature adjudication and acceptance remain separate. No count changes were made.
''')
x=json.loads((O/'input-bindings.json').read_text());rs={p:{'expected':h,'actual':H(Path(p))} for p,h in x.items()};assert len(rs)==33 and all(v['actual']==v['expected'] for v in rs.values())
put('integrity-after.json',{'pass':True,'count':len(rs),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'binding_file_sha256':H(O/'input-bindings.json'),'files':rs})
assert H(O/'original/proof-packet.zip')==x[str((O.parent/'fresh-corpus-r15/proof-packet.zip').resolve())]
assert H(O/'proof/FractionalDefect.lean')==x[str((O.parent/'fresh-corpus-r15/lean/FractionalDefect.lean').resolve())]
# Explicit allow-list: never package work/, generated tools, scripts for staging,
# or the dossier/receipt/manifest recursively.
names=['README.md','SUMMARY.md','results.json','paper.pdf','paper.tex','input-bindings.json','integrity-before.json','integrity-after.json','extraction.json','literal-verification.json','layout-verification.json','version-thesis-disposition.json','verify-manifest.py','replay-dossier.py']
for folder in ['original','proof','reviews','sources','provenance','replay']:
 names += [str(p.relative_to(O)) for p in (O/folder).rglob('*') if p.is_file()]
assert not any(n.endswith(('.olean','.ilean','.png','.aux','.xdv')) or '__pycache__' in n for n in names)
put('manifest.json',{n:{'sha256':H(O/n),'bytes':(O/n).stat().st_size} for n in sorted(names)})
p=subprocess.run(['python3',str(O/'verify-manifest.py')],capture_output=True,text=True);assert p.returncode==0,p.stderr;print(p.stdout)
with zipfile.ZipFile(O/'dossier.zip','w',zipfile.ZIP_DEFLATED) as z:
 for n in sorted(names+['manifest.json']):z.write(O/n,n)
with zipfile.ZipFile(O/'dossier.zip') as z:
 assert z.testzip() is None
 for n in names:assert hashlib.sha256(z.read(n)).hexdigest()==H(O/n)
 assert [n for n in z.namelist() if n.endswith('.zip')]==['original/proof-packet.zip']
put('dossier-receipt.json',{'sha256':H(O/'dossier.zip'),'bytes':(O/'dossier.zip').stat().st_size,'member_count':len(names)+1,'zip_crc_and_member_hash_verification':'PASS','manifest_sha256':H(O/'manifest.json'),'nonrecursive':True,'only_nested_zip':'original/proof-packet.zip','compiled_cache_render_intermediates':False})
print((O/'dossier-receipt.json').read_text())
