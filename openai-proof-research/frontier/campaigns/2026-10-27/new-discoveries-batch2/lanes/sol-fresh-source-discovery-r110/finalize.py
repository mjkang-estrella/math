from pathlib import Path
import hashlib,json,datetime
P=Path(__file__).resolve().parent;B=P.parent.parent
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(f):
 h=hashlib.sha256()
 with f.open('rb') as s:
  for b in iter(lambda:s.read(65536),b''):h.update(b)
 return h.hexdigest()
def dump(n,o):(P/n).write_text(json.dumps(o,indent=2)+'\n')
guard=P.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
assert sha(guard)=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
audit=json.loads((P/'duplicate-audit.json').read_text());assert audit['files']>127967
assert (P/'duplicate-corpus.jsonl').stat().st_size>1000000
rows=[]
for f in sorted((P/'sources').iterdir()):
 if f.is_file():rows.append({'path':str(f.relative_to(P)),'bytes':f.stat().st_size,'sha256':sha(f)})
dump('source-manifest.json',rows)
reg={'status':'HOLD','no_network_requests_in_r110':True,'last_known_omega':'73a5033dd654a16a14fcd1b13277f1a03d81d826','omega_commit_utc':'2026-10-29T19:55:36Z','last_known_openai':'7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a','openai_observed_utc':'2026-10-29T20:05:00Z','current_certificate':False,'old_300_cap_resolved':False,'reset_information':'r106/r107 saved HTTP receipts inspected; no usable rate-limit reset headers recorded','inherited_files':[]}
for lane,name in [('sol-fresh-source-discovery-r106','http.json'),('sol-fresh-source-discovery-r107','http.json'),('sol-fresh-source-discovery-r107','registry.json')]:
 f=P.parent/lane/name;o=json.loads(f.read_text());reg['inherited_files'].append({'path':str(f),'sha256':sha(f)})
for k in ['omega','openai']:
 f=P.parent/'root-edge-irregulator-final-freeze-r1'/f'{k}-tree.txt'
 reg[k+'_baseline']={'path':str(f),'sha256':sha(f),'interpretation':'complete old paths only; not current or semantic clearance'}
dump('registry.json',reg)
checks=json.loads((P/'check-results.json').read_text())
prov={'lane':P.name,'finalized_utc':now,'discovery_credit':0,'counts':{'additional':8,'total':38},'status':'UNRESOLVED; current registry freshness HOLD','claims':[{'source':'https://arxiv.org/html/2605.07628v2','labels':['Conjecture1','Conjecture2'],'status':'Unresolved full scope','gap':'Uniform preservation of relative interlacing and strictness for arbitrary admissible even/odd input pairs'},{'source':'https://arxiv.org/html/2608.12531v1','label':'Conjecture4.9','status':'Screened unresolved','gap':'No bound of excess Apéry maxima by dominance defect sigma'}],'duplicate_screen':{'files':audit['files'],'corpus':'duplicate-corpus.jsonl','mode':'all-date streaming hash and lexical report/embedded note screen','semantic_clearance':False,'literal_id_regex_controls':'PASS','failure_preserved':'audit-failed.guard.json records MemoryError at final serialization; fixed by streamed JSONL under unchanged caps'},'primary_sources':'source-manifest.json','http_receipts':'http.json','governing_context':'context-read.json','live_registry':'registry.json','exact_checks':{'replay':'sh run.sh','coefficient_lists':checks['b_candidates'],'Y_lists':checks['Y_candidates'],'stable_pairs':checks['stable_pairs'],'source_counterexamples':len(checks['source_counterexamples']),'symbol_obstruction':'exact, route-only','scope':'bounded diagnostics; no universal theorem'},'resource_guard':{'path':str(guard),'sha256':sha(guard),'unchanged':True,'AS_bytes':536870912,'group_RSS_bytes':536870912,'CPU_seconds':210,'wall_seconds':230,'nominal_sample_ms':40,'BLAS_threads':1},'strongest_objection':'Binomial/shifted-window tests may fail to imply the relative interlacing order for a different input; failed stronger symbol extension is not a source counterexample','limits':['Current public registry heads inaccessible by inherited single403 rate limits; no retries','Old300cap not resolved','Full semantic successor/registry coverage incomplete','No worldwide priority claim','No full proof or refutation'],'only_lane_writes':True,'no_children':True,'no_git':True,'no_browser_preview':True,'no_external_mutations':True,'no_lean_or_paper':True}
dump('provenance.json',prov)
for name in ['SUMMARY.md','progress.md']:
 with (P/name).open('a') as s:s.write(f'\nFinal expanded streaming audit: **{audit["files"]:,} files**. A serialization MemoryError was preserved and repaired with JSONL streaming under unchanged caps.\n')
with (P/'discovery.md').open('a') as s:s.write(f'\nFinal audit outcome: {audit["files"]:,} files; manifest duplicate-corpus.jsonl. The expanded first attempt failed with MemoryError during final JSON serialization (audit-failed.guard.json); initial successful screen and failed-empty manifest are retained. Repair streams each hash record to JSONL and passes the same guard. No caps raised.\n')
manifest=[]
for f in sorted(P.rglob('*')):
 if f.is_file() and '__pycache__' not in f.parts and f.name not in ['MANIFEST.sha256','manifest-check.log','finalize.log','finalize.guard.json']:
  manifest.append(sha(f)+'  '+str(f.relative_to(P)))
(P/'MANIFEST.sha256').write_text('\n'.join(manifest)+'\n')
print(json.dumps({'files_hashed':len(manifest),'audit_files':audit['files'],'credit':0,'counts':'8/38'}))
