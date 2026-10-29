from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).parent
H=lambda b:hashlib.sha256(b).hexdigest()
sources=[]
for p in sorted((L/'sources').rglob('*')):
 if p.is_file():sources.append({'path':str(p.relative_to(L)),'bytes':p.stat().st_size,'sha256':H(p.read_bytes())})
(L/'sourcebytes.sha256').write_text(''.join(f"{x['sha256']}  {x['path']}\n" for x in sources))
checks=json.loads((L/'check-results.json').read_text());a=L/'duplicate-expanded-summary.json'
audit=json.loads(a.read_text()) if a.exists() else {'status':'not completed; inspect audit-stream.guard.json and partial JSONL, no coverage claim'}
p={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'UNRESOLVED','credit':0,'counts':{'additional':8,'total':38},'primary_questions':[{'url':'https://arxiv.org/html/2609.13764v1','labels':['Conjecture7.4','Conjecture7.5','Conjecture8.5']},{'url':'https://arxiv.org/html/2603.11107v3','labels':['Conjecture1']}],'proof':False,'Lean':False,'paper':False,'sources':sources,'duplicate_files_initial':3268,'duplicate_stream':{'files':audit.get('files'),'hits':len(audit.get('hit_files',[])),'limit':'term triage only, not semantic clearance'},'registry':{'omega_HEAD':'73a5033dd654a16a14fcd1b13277f1a03d81d826','omega_committer_utc':'2026-10-29T19:55:36Z','delta_from_task_head':0,'openai_main':'7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a','wrong_initial_ref':'main returned d7af67136d4478875778ac6e75eb5fbb8b3693a5; expressly discarded for active-registry clearance','tree_failure':'403 rate limit, not retried','literal_current_body_pairs':4,'coverage':'inherited18:13 complete paths plus dated delta chains and8fresh literal bodies; not global semantic clearance; old300aggregate cap unresolved'},'helper_policy':{'guard':'../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py','sha256':H((L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py').read_bytes()),'AS_groupRSS_MiB':512,'CPU_s':210,'wall_s':230,'nominal_sample_ms':40,'BLAS_threads':1,'raised_caps':False,'unguarded_python':False},'preserved_failures':['wrong main ref','guessed irrational arxiv ID404','guessed original2013institutional URL404','original2013author connection refused and web timeout','current Omega recursive tree403','refresh JSONDecodeError after403','expanded whole-file audit MemoryError'],'check_scope':{'completion_m_max':5,'inputs':sum(x['inputs'] for x in checks['completion']),'inherited_identities':checks['inherited_occurrence_identities'],'D_n_max':8,'source_counterexample':False},'strongest_objection':'No universal source claim proved/refuted; original2013 and global semantic priority coverage incomplete','precise_gaps':['mixed-occurrence-safe bijective gap assignment or universal alternative growth injection','unimodality-preserving refined insertion-state argument','determinant-specific sufficient blocking beyond generic constraint counts']}
(L/'provenance.json').write_text(json.dumps(p,indent=2))
manifest=[]
for q in sorted(L.rglob('*')):
 if q.is_file() and q.name not in ['manifest.sha256','finalize.log','finalize.guard.json']:manifest.append(f'{H(q.read_bytes())}  {q.relative_to(L)}\n')
(L/'manifest.sha256').write_text(''.join(manifest));print(json.dumps({'sources':len(sources),'files':len(manifest),'duplicate_files':audit.get('files'),'duplicate_hits':audit.get('hit_files',[])},indent=2)[:20000])
# Freeze exact late duplicate receipt and input/context hashes, then refresh manifests.
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
f=R/'frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-euler-turan-final-review/fresh/trureturing/tools/scripts/agent/openproblem/SCREENED-OUT-R71.md'
(L/'sources/late-duplicate-SCREENED-OUT-R71.md').write_bytes(f.read_bytes())
p['dropped_target']={'label':'2609.13764 Conjecture8.5','status':'DROP_ALREADY_ATTEMPTED','receipt':str(f.relative_to(R)),'sha256':H(f.read_bytes()),'line':402,'reason':'same exact insertion-state nonclosure previously recorded; initial narrower screen missed embedded note'}
inputs=[R/'AGENTS.md',L.parent.parent/'AGENTS.md',L.parent.parent/'NEXT.md',L.parent.parent/'ledger.json',L.parent.parent/'prior-campaign-context.json',R/'sources/upstream.json',R/'sources/CONTENTS.md']
(L/'context-hashes.json').write_text(json.dumps([{'path':str(q),'sha256':H(q.read_bytes())} for q in inputs],indent=2))
sources=[]
for q in sorted((L/'sources').rglob('*')):
 if q.is_file():sources.append({'path':str(q.relative_to(L)),'bytes':q.stat().st_size,'sha256':H(q.read_bytes())})
p['sources']=sources;(L/'provenance.json').write_text(json.dumps(p,indent=2))
(L/'sourcebytes.sha256').write_text(''.join(f"{x['sha256']}  {x['path']}\n" for x in sources))
manifest=[]
for q in sorted(L.rglob('*')):
 if q.is_file() and q.name not in ['manifest.sha256','finalize.log','finalize.guard.json']:manifest.append(f'{H(q.read_bytes())}  {q.relative_to(L)}\n')
(L/'manifest.sha256').write_text(''.join(manifest))
print('FINAL',len(manifest),'files',len(sources),'sources; credit0; duplicate8.5 dropped')
