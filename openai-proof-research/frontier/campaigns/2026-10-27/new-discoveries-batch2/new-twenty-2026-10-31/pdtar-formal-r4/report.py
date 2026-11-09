from pathlib import Path
import hashlib,json,re,collections,zipfile
D=Path(__file__).resolve().parent
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
state=json.loads((D/'replay-state.json').read_text());m=json.loads((D/'manifest.json').read_text());mods=m['modules']; E=D/'replay/extracted'
assert len(state['steps'])==2*len(mods)+8==76
assert state['next']==76
before=json.loads((D/'frozen-before.json').read_text()); after={p:sha(D/p) for p in before};assert before==after
original=D.parent/'pdtar-formal-r3'
original_sha=sha(original/'pdtar-source.zip');assert original_sha=='8121c925f538aaa42b4a54c831c25d3d43fe3e4ef311d29e3704df0ddae7a4e0'
with zipfile.ZipFile(original/'pdtar-source.zip') as z:
 for p,h in before.items():
  assert hashlib.sha256(z.read(p)).hexdigest()==h==sha(original/p)
(D/'frozen-after.json').write_text(json.dumps(after,indent=2)+'\n')
receipts=[]
for i,step in enumerate(state['steps']):
 log=E/'logs'/(step['name']+'.log'); assert sha(log)==step['log_sha256']
 rc=json.loads(log.with_suffix('.receipt.json').read_text());receipts.append(rc)
 if i<69: assert step['returncode']==0
 else: assert step['returncode']!=0 and 'unsolved goals' in log.read_text()
auditstep=state['steps'][68];audit=(E/'logs'/(auditstep['name']+'.log')).read_text()
auditlines=[l for l in audit.splitlines() if l.startswith('DECL ')]
kinds=collections.Counter(re.search('kind=(\\w+)',l).group(1) for l in auditlines)
total=int(re.search(r'AUDIT_TOTAL (\d+); violations 0',audit).group(1));assert total==len(auditlines)
closure=int(re.search(r'CLOSURE_EQUALS_AUDITED (\d+)',audit).group(1));assert closure==len(mods)
for f,h in m['files'].items(): assert sha(D/f)==sha(E/f)==h
assert sha(D/'pdtar-source.zip')==state['zip_sha256']
modules=[dict(module='PDTAR.'+x,path='PDTAR/'+x+'.lean',sha256=sha(D/'PDTAR'/f'{x}.lean'),lines=len((D/'PDTAR'/f'{x}.lean').read_text().splitlines()),frozen=x in mods[:27],strict_compile=True,leanchecker=True) for x in mods]
neg=[dict(name=x['name'].split('-',1)[1],returncode=x['returncode'],false_claim_rejected=True,log=str((E/'logs'/(x['name']+'.log')).relative_to(D))) for x in state['steps'][69:]]
for n in neg:
 text=(D/n['log']).read_text()
 if n['name']=='NegK33Added': assert text.count('error:')==1 and '⊢ False' in text
newsource='\n'.join((D/'PDTAR'/f'{x}.lean').read_text() for x in mods[27:])
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b',newsource)
endpointlog=E/'logs'/(state['steps'][33]['name']+'.log'); assert "'PDTAR.mathdb_353203' depends on axioms: [propext, Classical.choice, Quot.sound]" in endpointlog.read_text()
r=dict(lane='pdtar-formal-r4',mathdb_id=353203,status='IMPLEMENTATION_COMPLETE_PENDING_ROOT_REVIEW',self_accepted=False,credit_claimed=0,endpoint=dict(name='PDTAR.mathdb_353203',module='PDTAR.FinalComplete',unconditional=True,exact_remaining_hypotheses=[],axioms=['propext','Classical.choice','Quot.sound'],axiom_log=str(endpointlog.relative_to(D))),targets=dict(starRigidityRemaining=True,threeThreeRigidityRemaining=True,twoWitnessRemaining=True),modules=modules,new_modules=['PDTAR.'+x for x in mods[27:]],total_lean_lines=sum(x['lines'] for x in modules),frozen_hashes_before=before,frozen_hashes_after=after,frozen_byte_identical=True,original_r3_archive_sha256_before=original_sha,original_r3_archive_sha256_after=original_sha,original_r3_modules_match=True,toolchain=dict(lean='4.34.1',mathlib_revision=m['mathlib_revision'],pins=m['pins'],read_only_cache=True),validation=dict(steps_completed=76,steps_total=76,fresh_extraction='replay/extracted',strict_rebuild_modules=34,leanchecker_modules=34,audit_total=total,audit_kinds=dict(kinds),audit_violations=0,audit_generated_declarations=True,audit_checks=['unsafe','partial','_unsafe_rec','implemented_by','extern','transitive axioms'],audited_modules=['PDTAR.'+x for x in mods],closure_equals_audited=True,closure_modules=closure,audit_log=str((E/'logs'/(auditstep['name']+'.log')).relative_to(D)),negative_controls=neg,peak_sampled_process_rss_bytes=max(x['sampled_process_rss_peak_bytes'] for x in receipts),max_step_wall_seconds=max(x['wall_seconds'] for x in receipts),limits='2 CPUs; CPU 120 s; wall 140 s; sampled RSS 6 GiB; MALLOC_ARENA_MAX=2; Lean -j1 -M3500; serial',rss_sampling_seconds=0.05,unsampled_transients_excluded=False),proof_route=dict(star='Singleton-opposite pair forts; component obstruction and pair-fort transposition; labelled equality in both orientations.',k33='All pairs PD and no singletons PD imply cubicity. A fort avoiding a singleton is its pair of non-neighbours; its closed neighbourhood misses exactly that singleton. This gives the balanced complete bipartition without graph enumeration.'),process_notes=['A premature 0.203-second import check failed for missing Final.olean while the inherited build driver had not finished. It did no elaboration; subsequent development and the entire fresh replay were serial.','An early fixed-vertex tuple proof attempt hit Lean\'s -M3500 allocation threshold (RSS 3673268224 bytes), retained in development logs. The final proof replaces that case expansion with symbolic reasoning; no limits were increased.','Intermediate failed elaborations printed sorryAx in diagnostics; no such declaration is in the final import closure. The fresh full audit checks the delivered certificate.'],artifacts={p:dict(path=p,sha256=sha(D/p)) for p in ['pdtar-source.zip','manifest.json','module-order.json','frozen-before.json','frozen-after.json','replay-state.json','STATEMENT-CORRESPONDENCE.md','REPRODUCE.md','SUMMARY.md','report.py']},child_agents=False,git_operations=False,external_actions=False,shared_ledger_edits=False,background_jobs_remaining=False)
(D/'results.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(dict(status=r['status'],audit_total=total,audit_kinds=dict(kinds),modules=closure,zip_sha256=state['zip_sha256'],peak_rss=r['validation']['peak_sampled_process_rss_bytes'],max_wall=r['validation']['max_step_wall_seconds']),indent=2))
