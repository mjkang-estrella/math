"""Produce a concise final handoff after both independent audits have passed."""
import sys
sys.dont_write_bytecode=True
import json,pathlib,collections,hashlib,datetime
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[2]
share=json.load(open(HERE/'share.json'))['keys'];r=json.load(open(HERE/'results_t14112.json'));checks=json.load(open(HERE/'checker_results.json'));cov=json.load(open(HERE/'coverage_summary.json'));ind=json.load(open(HERE/'independent_coverage.json'))
assert set(r)==set(share),(len(r),len(share))
certs=sorted((HERE/'certs').rglob('*.jsonl'))
for p in certs:
 fn=str(p.relative_to(HERE));sha=hashlib.sha256(p.read_bytes()).hexdigest()
 for kind in ('hd','v14'):
  q=checks[fn+'::'+kind];assert q['status']=='PASS' and q['certificate_sha256']==sha,(fn,kind,q['status'])
 for line in list(open(p))[1:]:
  n=json.loads(line)
  if n['k']=='l':assert set(n['x']) in ({'prime'},{'sz','sol'}),(fn,n['x'])
closed=sorted(k for k,v in r.items() if v['status']=='CLOSED');opened=sorted(set(share)-set(closed))
assert set(closed)==set(ind['closed_configurations'])
assert all(cov[k]['directly_validated_certificates']==cov[k]['expected_certificates'] for k in closed)
passes=collections.Counter(v['status'] for v in checks.values())
summary={'target':14112,'share':'zero-based odd indices of sorted original BUDGET keys','assigned':len(share),'closed':len(closed),'still_open':len(opened),'closed_keys':closed,'still_open_keys':opened,'certificates':len(certs),'checker_verdicts':dict(passes),'all_certificates_directly_checked':True,'new_kill_types':False,'independent_cover':'independent_coverage.json'}
json.dump(summary,open(HERE/'summary.json','w'),indent=1)
lines=['# Codex3b final research report','','**PROVED (checked certificate covers), COMPUTED (counts).**',f'Assigned: {len(share)} configurations of t=14112; closed: {len(closed)}; still open/BUDGET: {len(opened)}.',f'{len(certs)} ordinary nd certificates passed both checkers directly: {2*len(certs)} PASS verdicts. No new kill type and no checker changes.','', 'Every closed configuration has an independently replayed E slice cover and complete far-digit ordering coverage. All generated certificates, including any partial configuration slices, were checked. Each closed configuration is covered from its original qmin=3 domain, so no finite exceptional placement is left. The prior E lattice enumeration through 600 digits is hashed for context and was not rerun.','','Closed keys:']+['- `'+k+'`' for k in closed]+['','Files:','- `summary.json`: exact closed/open lists.','- `share.json` and `baseline.json`: exact original assignment and source hash.','- `results_t14112.json`, `stage_*.json`, and logs: checkpointed attempts and diagnostics.','- `certs/t14112/`: complete certificate trees only.','- `checker_results.json`, `logs/checks/`: direct checker commands, hashes, verdicts and timings.','- `coverage_summary.json`, `independent_coverage.json`: slice/domain/order audit.','- `supply_search.json`, `supply_extended.json`, `period_strengths.json`: prime supply work.','- `manifest.json`: hashes.','','All remaining configurations are BUDGET; no nonexistence claim follows. No files outside codex3b and notes/highdim_codex3b.md were written by this continuation. No git commit was made.']
text='\n'.join(lines)+'\n';(HERE/'REPORT.md').write_text(text)
notes=ROOT/'notes/highdim_codex3b.md'
with open(notes,'a') as f:f.write('\n## Final checked handoff\n\n'+text)
print(json.dumps({k:v for k,v in summary.items() if k not in ('closed_keys','still_open_keys')},indent=1))
