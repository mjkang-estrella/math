from pathlib import Path
import hashlib,json,sqlite3,time
L=Path(__file__).resolve().parent;R=L.parents[5];db=sqlite3.connect(L/'audit.sqlite')
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(131072),b''):h.update(b)
 return h.hexdigest()
old=L.parent/'sol-fresh-source-discovery-r115/audit-manifest.jsonl';same=changed=missing=0
for line in old.open():
 d=json.loads(line);cur=db.execute('select sha from done where path=?',(d['path'],)).fetchone()
 if not cur:missing+=1
 elif cur[0]==d['sha256']:same+=1
 else:changed+=1
coverage={'original_paths':db.execute('select count(*) from done').fetchone()[0],'unique_sha256':db.execute('select count(distinct sha) from done').fetchone()[0],'bytes':db.execute('select sum(size) from done').fetchone()[0],'r115_metadata_validation':{'old_manifest_sha256':sha(old),'same_current_hash':same,'different_current_hash':changed,'not_in_current_text_scope':missing,'note':'Prior manifest has no mtime. Every in-scope original was freshly hash-validated; target semantics freshly streamed. Current size/mtime allow bounded continuations. No inherited semantic clearance.'},'categories':{},'exclusions':'excluded-echoes.jsonl enumerates generated metadata/content echoes without content ingestion; .git/.lake/node_modules/__pycache__ and own lane omitted','gaps':['PDF/binary-only bodies without text not searched','JSONL excluded conservatively; could contain original research not represented in retained text; no full absence assertion','historical search/catalogue/transcript JSON technically scanned is not mathematics','live concurrent changes after scan not frozen globally'],'reconciliation':'Exact Gaussian duplicate r47 rejected; old Matkowski373182 equation is distinct; no matching actual paranorm-research body located in screened originals'}
for tag,sql in {'SCREENED-OUT':"path like '%SCREENED-OUT%'",'reviews_and_copied_context':"lower(path) like '%review%' or path like '%/context/%'",'proofs':"path like '%/PROOF.md'",'tools_scripts_agent_openproblem':"path like '%/tools/%' or path like '%/scripts/%' or lower(path) like '%agent%' or lower(path) like '%open%problem%'",'all_campaigns':"path like 'frontier/campaigns/%'"}.items():coverage['categories'][tag]=db.execute('select count(*) from done where '+sql).fetchone()[0]
(L/'coverage.json').write_text(json.dumps(coverage,indent=2)+'\n')
http=[json.loads(s) for s in (L/'http.jsonl').open()]
prov={'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'lane':str(L),'role':'solo research; no children','model':'GPT-6.1 Sol high; default service speed requested','counts':{'additional':8,'total':38,'next':39,'credit':0},'target':'Matkowski JCA33(2026)293-301 Conjecture2.4','disposition':'UNRESOLVED; no nomination or PROOF.md','primary_sha256':sha(L/'sources/matkowski.pdf'),'http_receipts':'http.jsonl','source_failures':[x for x in http if 'error'in x],'registry':{'omega':'ab0fa0287d4fcc5416699ceb07e4ce97ffbff4b4','openai':'7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a','scope':'complete baseline path metadata plus structural deltas and selected actual bodies; semantic freshness HOLD'},'resource_guard':{'path':str(L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),'sha256':sha(L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),'AS_and_group_RSS_MiB':512,'CPU_seconds':210,'wall_seconds':230,'sample_ms':40,'BLAS_threads':1},'failures_and_corrections':['bs4 import failed (ModuleNotFoundError); standard HTMLParser corrected it; original tool failure transcribed in progress.md','initial registry script used350009 earlier baseline and wrong delta pathname; original registry-run.log retained; corrected350197 baseline and cached delta in registry-corrected.log','initial web request of nonexistent arxivv2 returned404; current primary abs authenticates v1 only','guessed AMS1990 URL404 and author-record timeout retained; no source clearance inferred'],'external_posting_accounts_browser_git_shared_edits':False,'worldwide_priority_claim':False}
(L/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
with (L/'manifest.jsonl').open('w') as out:
 for p in sorted(L.rglob('*')):
  if p.is_file() and p.name not in {'manifest.jsonl','manifest-verification.json','seal.log'}:
   out.write(json.dumps({'path':str(p.relative_to(L)),'bytes':p.stat().st_size,'sha256':sha(p)})+'\n')
ok=n=True
count=0
for line in (L/'manifest.jsonl').open():
 d=json.loads(line);assert sha(L/d['path'])==d['sha256'];count+=1
(L/'manifest-verification.json').write_text(json.dumps({'entries':count,'all_hashes_verified':True,'manifest_sha256':sha(L/'manifest.jsonl')},indent=2)+'\n')
print(json.dumps({'manifest_entries':count,'coverage':coverage}))
