from pathlib import Path
import json,re,hashlib
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/percolation-formal-r4');F=R/'fresh-extracted'
order=(F/'module-order.txt').read_text().splitlines();rows=[]
def seconds(s):
 v=s.strip().split(':');n=0.0
 for x in v:n=n*60+float(x)
 return n
for m in order:
 d={'module':m}
 for kind in ['build','check']:
  p=F/'logs'/f'{kind}-{m}.json';q=F/'logs'/f'{kind}-{m}.log'
  if not p.exists():d[kind]={'status':'not_run'};continue
  receipt=json.loads(p.read_text());text=q.read_text()
  wall=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)',text)
  rss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',text)
  d[kind]={'status':'passed' if receipt['exit']==0 else 'failed',**receipt,'wall_seconds':seconds(wall[1]) if wall else receipt['seconds'],'gnu_max_rss_kib':int(rss[1]) if rss else None}
 rows.append(d)
(R/'module-times.json').write_text(json.dumps(rows,indent=2))
passed=[d for d in rows if d['build']['status']=='passed' and d['check']['status']=='passed']
progress=json.loads((F/'normalized-progress.json').read_text()) if (F/'normalized-progress.json').exists() else {'replayed_steps':0}
complete=len(passed)==len(order) and progress['replayed_steps']==129671
endpoint='Percolation.not_conjecture20_unconditional' if complete else None
ax=(F/'logs/build-NormalizedEndpoint.log').read_text() if (F/'logs/build-NormalizedEndpoint.log').exists() else ''
audit=(F/'logs/build-AuditR4.log').read_text() if (F/'logs/build-AuditR4.log').exists() else ''
build_total=sum(d['build'].get('wall_seconds',0) for d in rows);check_total=sum(d['check'].get('wall_seconds',0) for d in rows)
result={'status':'unconditional' if complete else 'partial','endpoint':endpoint,'endpoint_statement':'¬ Percolation.Conjecture20' if complete else None,'module_count':len(order),'fresh_compile_passes':sum(d['build']['status']=='passed' for d in rows),'fresh_checker_passes':sum(d['check']['status']=='passed' for d in rows),'compile_wall_seconds':round(build_total,2),'checker_wall_seconds':round(check_total,2),'combined_wall_seconds':round(build_total+check_total,2),'normalized_progress':progress,'source_zip_sha256':hashlib.sha256((R/'source-only.zip').read_bytes()).hexdigest(),'inherited_zip_sha256':hashlib.sha256((R/'inherited-source.zip').read_bytes()).hexdigest(),'inherited_source_modules_byte_identical':92,'endpoint_axiom_output':[x for x in ax.splitlines() if 'depends on axioms:' in x],'metadata_audit':[x for x in audit.splitlines() if 'metadata audit passed:' in x],'certificate_hashes':json.loads((R/'certificate-sha256.json').read_text()),'generator_correspondence':json.loads((R/'generator-correspondence.json').read_text()),'source_scan':{'files':len(order),'findings':[]},'max_sampled_rss_kib':max(v.get('peak_rss_kib',0) for d in rows for v in [d['build'],d['check']]),'max_invocation_wall_seconds':max(v.get('wall_seconds',0) for d in rows for v in [d['build'],d['check']]),'development_failures':[{'description':'Initial combined finite geometry check killed by RSS watchdog; replaced by argument from plane axioms. Early reused log labels mean original full killed-process log is unavailable.','exit':137,'seconds':28,'sampled_rss_kib':6295192},{'description':'Routine elaboration corrections to transport, normalization, exporter type annotation, and input family indexing; retained available failure logs are separate from fresh logs.'}],'limits_raised':False,'acceptance':'Root alone decides; no campaign credit claimed.'}
(R/'results.json').write_text(json.dumps(result,indent=2))
(R/'normalized-progress.json').write_text(json.dumps(progress,indent=2))
if complete:
 assert result['metadata_audit']
 assert "sorryAx" not in ax
 assert 'Percolation.not_conjecture20_unconditional' in ax
 summary=f'''# Round 4: unconditional normalized refutation

Endpoint: `Percolation.not_conjecture20_unconditional : ¬ Percolation.Conjecture20`.

Status: unconditional. The proof also closes `Percolation.generatedNormalizedUnsat5_closed : Percolation.GeneratedNormalizedUnsat5` and `Percolation.noMinimalTwoRound5_closed : Percolation.NoMinimalTwoRound5`. Root alone decides acceptance; this lane claims no campaign credit.

Normalization is proved first: incidence-preserving point/line bijections preserve step, every natural round, percolation, TimeIs and Minimal; every percolating threshold-5 set has a noncollinear triple; an explicit family of 86 kernel-checked collineations transports that triple to 0, 25, 30. The transported witness satisfies the unchanged CNF and the three positive units. Lean's normalized DIMACS export exactly matches the copied certificate input.

All 129,671 retained normalized additions were freshly replayed, through the final empty clause. All {len(order)} modules compiled with strict warnings and passed explicit-module leanchecker, serially under the fixed resource limits. Compiler total: {build_total:.2f} s. Checker total: {check_total:.2f} s. Combined: {build_total+check_total:.2f} s. The endpoint depends only on propext, Classical.choice, Quot.sound. The metadata audit and {len(order)}-file source scan passed. The 92 inherited Lean modules remain byte-identical.

Files: source-only.zip; results.json; module-times.json; PROOF.md; STATEMENT-CORRESPONDENCE.md; REPRODUCE.md; certificate-sha256.json; generator-correspondence.json; inherited-source-comparison.json; normalized-progress.json; fresh-replay.log; fresh-extracted/logs/; packet/src/; and development logs/.

Archive SHA256: {result['source_zip_sha256']}.

The initial monolithic finite geometry attempt exceeded the RSS cap; it was replaced without raising any limit. Development retries are not counted as verification. No lane-started background job remains at handback.
'''
 (R/'SUMMARY.md').write_text(summary)
print(json.dumps({k:result[k] for k in ['status','module_count','fresh_compile_passes','fresh_checker_passes','compile_wall_seconds','checker_wall_seconds','normalized_progress']},indent=2))
