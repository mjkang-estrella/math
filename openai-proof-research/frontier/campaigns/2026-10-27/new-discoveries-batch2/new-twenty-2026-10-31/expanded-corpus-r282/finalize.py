from pathlib import Path
import hashlib,json,datetime,resource,os,re
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
p=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest();rs=json.loads((p/'results.json').read_text());reservation=json.loads((p/'reservation.json').read_text());assert list(rs)==list(map(str,reservation['ids']))
version_inventory={}
for f in sorted((p/'sources').glob('*.abs.html')):
 t=f.read_text();version_inventory[f.name]={'versions_listed':re.findall(r'\[v(\d+)\]',t),'sha256':sha(f.read_bytes()),'warning':'History extraction not proof/correction clearance; latest unversioned PDF plus earlier versions fetched where listed in source inventory.'}
(p/'versions.json').write_text(json.dumps(version_inventory,indent=2))
text='''# r282 research handback

All 20 immutable assigned records were literally read and extracted. No new full-scope solution or qualified Pi execution task was obtained. No accepted credit is claimed; the shared campaign ledger remains untouched (52/60 at intake).

`results.json` has exactly the reserved 20 ID keys. Each contains the complete parsed record, exact statement, one-based raw-line location, original chunk/raw/statement SHA256, actual review depth, disposition, source hashes, and remaining gap. `raw/*.jsonl` preserves original newline bytes. `ORDINARY_ATTEMPTS.md` develops three ordinary routes each for the cover inequality, (A4), and the connected PED cycle bound; it states the precise failed steps. No CANDIDATE.md is warranted.

## Important exclusions

Pan's cited paper already proves 374161 in exact scope (Theorem 1.2; main proof body read). The pinned OpenAI strong thin-tree theorem already implies 388066 by f(epsilon)=max(1,ceil(C/epsilon)); this is an explicit source bridge exclusion. For 374223, minimal elements of a poset with least element 0 form the singleton {0}, but the source asks about minimal prime ideals with their Zariski topology. That literal triviality is an excluded definition correction. For 388676, the collinear-centre infinite-tangent loophole is already printed in the Illinois source; the intended cubic extremal construction remains unpaid. None receives new credit.

## Exact assignment dispositions

| ID | Disposition | Precise remaining issue |
|---|---|---|
'''
for k,v in rs.items():text+=f"| {k} | {v['disposition']} | {v['ordinary_attempts_and_precise_gap']} |\n"
text+='''
## Historical reconciliation

Read applicable project/batch/campaign AGENTS, full TASK, project upstream pin, catalogue routing matches, current campaign ledger/status, batch ledger and prior-campaign context. Searches in `history-matches.txt` and `history-source-matches.txt` cover bounded historical prose/results ID/title/source-family matches, with truncation/glob limits documented in `history-command.json`. Absence is not novelty clearance. The relevant substantive same-source predecessors are r279 on PED unrestricted classification (375790) and r280 on translation-oval spread classification (325668). Their actual result entries were read and their unresolved obstructions retained. Metadata reservations and unrelated numeric/string matches are not proof outcomes. Existing thin-tree catalogue entries are an exact source-family exclusion. No historical assignment was changed.

## Current registries and source depth

`registry-screen.json` records current public raw OpenAI catalogue, trureturing release page, LeanPool import index AND projects.yml screens, plus public repository-page heads. Observed heads: OpenAI `4eaee87548250b2682affda7d05d947c05554bae`; trureturing `48ae8c6f5fe7453939a66c72f0ab4ecbb64f475c`; LeanPool head is recorded in the JSON. These are routing screens, not a complete current tree or all-code reading. Broad “gonality” substring hits include orthogonality false positives; “Cartier”, “dyadic” and “Ramanujan” also retrieve unrelated subjects. No global clearance follows from these screens. No GitHub API request was made, and no denied API route was retried.

`receipts.json` and individual receipt files contain URL, UTC, HTTP status/error and raw response SHA256. Egres primary requests timed out; Saint-Flour notes returned 404. ArXiv source histories are in `versions.json`. Earlier versions were fetched for cover (v1–v4 in addition to current v5), tree ILD (v1 plus v2), and Woo–Yong (v1 plus v2); other assigned arXiv histories list v1. Cover journal body was fetched and its target is Conjecture 16; all five arXiv target passages were compared. Other journal/correction/withdrawal and citing-proof-body coverage remains incomplete. Search results are leads, not body review. This packet makes no claim to have read every cited proof or every downloaded page. Figures were not visually reviewed; only textual captions, recipes and surrounding definitions were read. Exact per-ID limits are in results and ordinary attempts.

## Integrity and execution

Reservation SHA256 before and after: `fe81d408b47d501044d0352db06f5771594aa0b073994d3e2fb1382a8d854131`, matching reservation.sha256. No reselection/reservation command ran. `reservation-check-before.json`, `reservation-check-after.json`, `verification.json`, and `MANIFEST.sha256` provide the integrity record.

Only this lane was written. No child, git action, shared ledger or author edit, publication, upload, contacts, account/browser action, Lean build, solver, numerical computation or heavy enumeration occurred. Fetch/text/hash scripts are retained with actual paths and receipts; they ran to completion. Resource enforcement and its limits are recorded in `resource-log.json`: fetches had CPU120/AS6GiB/wall140 caps but no two-CPU affinity enforcement; this is disclosed rather than retroactively certified. Assembly/finalization enforce two-CPU affinity. No background process was launched or remains from this task. Initial short extraction/inventory commands used inline Python; retained actual-path scripts cover the network jobs and final assembly/verification.

All novelty, significance, literal Lean, independent review, manuscript and fresh replay gates remain open for any future new candidate. Pi execution requires a concrete new root assignment.
'''
(p/'SUMMARY.md').write_text(text)
(p/'UPDATED_BRIEF.md').write_text('# Full task brief and handback state\n\n'+(p/'TASK.txt').read_text()+'\n\n# Research state\n\n'+text)
checks=[];chunks={}
for k,v in rs.items():
 q=v['provenance'];raw=(p/q['raw_file']).read_bytes();assert raw.endswith(b'\n');assert sha(raw)==q['raw_sha256'];assert json.loads(raw)==v['full_parsed_record'];assert sha(v['literal_statement'].encode())==q['statement_utf8_sha256'];chunks[q['chunk']]=q['chunk_sha256'];checks.append(k)
for f,h in chunks.items():assert sha(Path(f).read_bytes())==h
h=sha((p/'reservation.json').read_bytes());assert h==(p/'reservation.sha256').read_text().split()[0];assert h==json.loads((p/'reservation-check-before.json').read_text())['sha256']
(p/'verification.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exact20_keys':checks,'raw_newlines_parsed_records_statement_hashes_verified':True,'original_chunk_hashes_rechecked':chunks,'reservation_before_after_matches':True,'reservation_sha256':h,'no_live_task_sessions':'All three fetch sessions and assembly returned exit_code=0; no background processes launched.'},indent=2))
manifest=[]
for f in sorted(p.rglob('*')):
 if f.is_file() and f.name!='MANIFEST.sha256':manifest.append(sha(f.read_bytes())+'  '+str(f.relative_to(p)))
(p/'MANIFEST.sha256').write_text('\n'.join(manifest)+'\n');print('PASS: exact20, all raw/chunk/statement hashes, immutable reservation; manifest files',len(manifest))
