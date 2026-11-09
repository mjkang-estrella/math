from pathlib import Path
import hashlib,json,re
L=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ebc-formal-r1')
R=L/'replay-final';mods=(L/'module-order.txt').read_text().split();records=[]
for m in mods:
 rec={'module':m,'pass':(R/f'logs/{m}.PASS').exists()}
 for k in ['lean','checker']:
  p=R/f'logs/{m}.{k}.log';s=p.read_text() if p.exists() else ''
  matches=re.findall(r'CAP exit=(\d+) peak_rss_kib=(\d+) wall_s=(\d+)',s)
  rec[k]={'log':str(p.relative_to(L))}
  if matches:
   code,rss,wall=map(int,matches[-1]);rec[k].update(exit_code=code,peak_rss_kib=rss,wall_seconds=wall)
  else:rec['pass']=False
 records.append(rec)
audit=(R/'logs/Audit.lean.log').read_text();scan=json.loads((L/'logs/source-scan.json').read_text())
res={'mathdb':337062,'status':'conditional','credit_claimed':0,
 'endpoint':'EBC337062.conjecture21_false',
 'statement':'EBC337062.DistanceAndCounts → EBC337062.PathSplitting32 → ¬ EBC337062.Conjecture21',
 'remaining_props':['EBC337062.DistanceAndCounts','EBC337062.PathSplitting32'],
 'module_count':len(mods),'strict_fresh_extracted_replay_pass':all(r['pass'] for r in records),
 'modules':records,'source_scan_pass':scan['pass'],
 'metadata_audit_pass':'AUDIT PASS:' in audit,
 'endpoint_axioms':['propext','Classical.choice','Quot.sound'],
 'nonvacuity_control':'EBC337062.control_uniform',
 'archive':'source-only.zip','archive_sha256':hashlib.sha256((L/'source-only.zip').read_bytes()).hexdigest(),
 'limitations':['General path-splitting theorem not proved','BFS layer correctness with respect to literal graph paths not proved','No acceptance or novelty claim; unread 2022 follow-up remains root matter'],
 'development_failures':['Broad Mathlib import exceeded RSS cap; imports narrowed','Monolithic rational evaluation exceeded CPU cap; split into eight modules with unchanged caps','Development elaboration and strict-warning errors retained in logs'],
 'no_background_jobs_at_handback':True}
(L/'results.json').write_text(json.dumps(res,indent=2)+'\n')
assert res['strict_fresh_extracted_replay_pass'] and res['metadata_audit_pass'] and res['source_scan_pass']
print(json.dumps({k:res[k] for k in ['status','module_count','strict_fresh_extracted_replay_pass','metadata_audit_pass','source_scan_pass']}))
