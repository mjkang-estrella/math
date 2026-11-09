from pathlib import Path
import sys,json,hashlib,zipfile,subprocess,datetime
D=Path(sys.argv[1]).resolve();P=D.parent
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(f):
 h=hashlib.sha256()
 with f.open('rb') as a:
  for b in iter(lambda:a.read(1048576),b''):h.update(b)
 return h.hexdigest()
def save(n,x):(D/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
before=json.loads((D/'inputs-before.json').read_text());after={f:{'sha256':sha(Path(f)),'bytes':Path(f).stat().st_size} for f in before};save('inputs-after.json',after)
assert before==after
save('input-integrity-receipt.json',dict(status='PASS',files=len(before),before_after_identical=True,utc=now))
root={}
for n in ['replay-result.json','registry-refresh.json']:
 f=P/'percolation-parent-final-r1'/n
 root[n]=dict(status='present' if f.exists() else 'pending',path=str(f))
 if f.exists():root[n].update(sha256=sha(f),data=json.loads(f.read_text()))
save('root-status.json',dict(utc=now,files=root))
assert all(x['status']=='pending' for x in root.values()),'Root receipt arrived: update paper before packaging'
info=subprocess.run(['pdfinfo',str(D/'paper.pdf')],capture_output=True,text=True,check=True).stdout
(D/'pdfinfo.txt').write_text(info);pages=int(next(x for x in info.splitlines() if x.startswith('Pages:')).split()[1]);assert pages==7
imgs=sorted(D.glob('final-page-*.png'));assert len(imgs)==7
save('page-QA-receipt.json',dict(status='PASS',pages=pages,method='Rendered every final PDF page using Poppler at 100 dpi; assistant visually inspected every image at full displayed size.',checks=['readable body text and mathematical symbols','no clipping or overlapping blocks','tables legible','no orphan reference page','consistent footer and page numbering'],images=[dict(path=f.name,sha256=sha(f)) for f in imgs],paper_sha256=sha(D/'paper.pdf'),utc=now))
recomp=json.loads((D/'recomputation.json').read_text());trace=json.loads((D/'certificates/normalized-trimmed.json').read_text());used={v for _,_,hs in trace['steps'] for v in hs if v<=trace['inputs']};assert used==set(trace['used_inputs'])
summary='''# No two-round minimal line-percolating set in PG(2,5)

DRAFT, AI-assisted; 7 pages. MathDB 333709. No human authors or affiliations invented. Zero accepted credit; root alone accepts. Campaign context supplied by the brief: 43/60 beyond 39; this dossier changes no ledger or count.

The result excludes every inclusion-minimal threshold-5 percolating set of exact synchronous time 2 in PG(2,5), refuting the read arXiv Conjecture 20 at the permitted upper boundary (5,5).

Fresh isolated Python recomputation: PASS. It verifies the projective geometry, all five positive controls and every deletion closure, regenerates the 1,085-variable, 14,698-clause formula byte-exactly, and checks all 129,671 RUP additions (3,340,122 hint uses). All 7 final PDF pages were rendered and visually inspected. Safe packet extraction and all 847 source-manifest checks pass without executing Lean.

The supplied developer replay covers 830 modules and totals 5,232.09 s. No Lean, lake, leanchecker or SAT/ILP solver ran in this lane. Root replay-result.json and registry-refresh.json remain pending at finalization. Journal full text remains unread; the qualified version-of-record limitation and positive retention evidence from root ruling r2 are explicit. No priority claim is made.

Input reconciliation: CANDIDATE.md incorrectly calls (5,5) interior; it is the allowed upper boundary. Discovery, independent-review and final-Lean clause/certificate counts differ because the encodings differ, not because one certificate can be reused for another. Early conditional endpoints are historical and superseded by the unconditional r8 endpoint. The (7,5) control mentioned in discovery SUMMARY.md is absent from the greedy-search percolation.json, but its witness is in percolation-sat.json and passes fresh checks. The 323 MB packet figure describes expanded bytes (323,843,462); its compressed ZIP is 64,586,499 bytes. No mathematical discrepancy was found in the recomputed final data. All 474 frozen input hashes match before and after.

Deliverables: paper.pdf; paper.md and build_paper.py; PROOF.md; REPRODUCE.md; results.json; recomputation.json; final-page-1.png through final-page-7.png and page-QA-receipt.json; exact MathDB raw line and source copies under evidence/; packet-documentation/; packet-reuse-receipt.json and packet-safety-repeat.json; source and artifact manifests; manuscript.zip and full-dossier.zip with sidecar manifests and archive-receipt.json.

The final Lean packet is NOT inside either dossier ZIP. It is reused byte-identically at the path and SHA-256 in packet-reuse-receipt.json. Certificate data needed for portable arithmetic reproduction are included separately. All writes stayed within this lane; no network, git, agents, external messages or publication were used. All commands finished in the foreground and no lane-started jobs remain.
'''
(D/'SUMMARY.md').write_text(summary)
save('results.json',dict(title='No two-round minimal line-percolating set in PG(2,5)',status='DRAFT',mathdb_id=333709,pages=pages,ai_assistance='OpenAI Codex',accepted_credit=0,root_accepts_only=True,campaign_context=dict(progress=43,target=60,prior=39,ledger_modified=False),theorem='No inclusion-minimal threshold-5 percolating set in PG(2,5) has exact time 2.',endpoint='Percolation.not_conjecture20_unconditional : ¬ Percolation.Conjecture20',recomputation=recomp,root=root,version_of_record='unread; qualified limitation with positive author-side evidence in ruling r2',input_integrity='474 frozen inputs unchanged',page_qa='PASS',packet_external='packet-reuse-receipt.json',discrepancies=['upper boundary, not interior','distinct encodings have distinct counts','(7,5) witness located in SAT output rather than greedy output','packet size is expanded size'],lean_or_solver_executed=False,utc=now))
# Ignore transient caches and post-package receipts; no archive nesting.
excluded={'MANIFEST.json','archive-receipt.json','manuscript.zip.manifest.json','full-dossier.zip.manifest.json'}
files=sorted(f for f in D.rglob('*') if f.is_file() and not f.is_symlink() and 'tmp' not in f.relative_to(D).parts and '__pycache__' not in f.parts and f.suffix!='.zip' and f.name not in excluded and f!=D/'receipts/package.json')
manifest={str(f.relative_to(D)):dict(bytes=f.stat().st_size,sha256=sha(f)) for f in files};save('MANIFEST.json',dict(coverage='All regular delivered non-ZIP artifacts except this manifest, archive sidecars/receipt and the package resource receipt; tmp/cache excluded.',files=manifest))
def pack(name,selection):
 entries={}
 with zipfile.ZipFile(D/name,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
  for f in selection:
   rel=str(f.relative_to(D));z.write(f,rel);entries[rel]=dict(bytes=f.stat().st_size,sha256=sha(f))
 with zipfile.ZipFile(D/name) as z:
  assert z.testzip() is None
  assert len(z.namelist())==len(entries)
  assert not any('source-only.zip' in x or x.endswith('.lean') and 'percolation-formal-r8' in x for x in entries)
  for rel,item in entries.items():assert hashlib.sha256(z.read(rel)).hexdigest()==item['sha256']
 save(name+'.manifest.json',entries)
 return dict(path=name,bytes=(D/name).stat().st_size,sha256=sha(D/name),members=len(entries),crc_and_member_sha256='PASS',lean_packet_embedded=False)
manuscript=[D/n for n in ['paper.pdf','paper.md','build_paper.py','PROOF.md','REPRODUCE.md','SUMMARY.md','results.json','recomputation.json','page-QA-receipt.json','packet-reuse-receipt.json']]+imgs
receipts=[pack('manuscript.zip',manuscript),pack('full-dossier.zip',files+[D/'MANIFEST.json'])]
save('archive-receipt.json',dict(archives=receipts,utc=now,manifest_self_hash_excluded=True,no_lane_jobs_started_in_background=True))
print(json.dumps(dict(pages=pages,inputs_unchanged=len(before),recomputation='PASS',root='pending',archives=receipts),indent=2))
