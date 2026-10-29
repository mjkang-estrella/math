from pathlib import Path
import json,hashlib,datetime,platform
P=Path(__file__).resolve().parent;R=Path('openai-proof-research').resolve()
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
context=['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','frontier/campaigns/2026-10-27/new-discoveries-batch2/AGENTS.md','frontier/campaigns/2026-10-27/new-discoveries-batch2/NEXT.md','frontier/campaigns/2026-10-27/new-discoveries-batch2/ledger.json','frontier/campaigns/2026-10-27/new-discoveries-batch2/prior-campaign-context.json']
log=[]
for n in ['http.json','registry-http.json','more-http.json']:log.extend(json.loads((P/n).read_text()))
audit=json.loads((P/'duplicate-audit.json').read_text())
provenance=dict(lane=P.name,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='UNRESOLVED',credit=0,counts=dict(additional=8,total=38),context_sha256={x:sha(R/x) for x in context},source_requests=log,source_files=[dict(path=str(f.relative_to(P)),bytes=f.stat().st_size,sha256=sha(f)) for f in sorted((P/'sources').iterdir()) if f.is_file()],heads={k:json.loads((P/'sources'/(k+'_head.json')).read_text())['sha'] for k in ['omega','openai']},duplicate_screen=dict(files=audit['files'],unique_contents=audit['unique_contents'],initial_files=4791,initial_unique_contents=2740,expanded_review_path_files=True,interpretation='No previous selected claim attempt found; expanded inverse match is unrelated symplectic bibliography; expanded GIT matches are namesakes/unrelated numbered conjectures or citations'),coverage_holds=['publisher VoR403','initial baseline-to2130 comparison300-file cap','lexical screening not exhaustive current semantic audit'],resource=dict(guard_sha256=sha(P/'helper_guard.py'),AS_and_group_RSS_bytes=536870912,CPU_seconds=210,wall_seconds=230,nominal_sample_ms=40,BLAS_threads=1,cap_raises=False,sampled_RSS_not_continuous=True),python=platform.python_version(),proof=False,lean=False,paper=False,external_mutations=False,shared_edits=False,git_operations=False)
(P/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
(P/'sourcebytes.sha256').write_text(''.join(sha(f)+'  '+str(f.relative_to(P))+'\n' for f in sorted((P/'sources').iterdir()) if f.is_file()))
(P/'manifest.sha256').write_text(''.join(sha(f)+'  '+str(f.relative_to(P))+'\n' for f in sorted(P.rglob('*')) if f.is_file() and f.name!='manifest.sha256' and '__pycache__' not in f.parts))
print('finalized',len(provenance['source_files']),'source files;',audit['files'],'duplicate-screen files')
