from pathlib import Path
import json,hashlib,collections,shutil,os,datetime
r=Path(__file__).resolve().parents[1]
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
build=json.loads((r/'development-state.json').read_text());val=json.loads((r/'development-validation.json').read_text());fresh=json.loads((r/'fresh-final/replay-state.json').read_text());initial=json.loads((r/'fresh-extracted/replay-state.json').read_text());fixes=json.loads((r/'source-fixes.json').read_text());mods=json.loads((r/'modules.json').read_text());closure=json.loads((r/'closure.json').read_text())
assert all('build:'+m in build['done'] for m in closure)
counts=collections.Counter(k.split(':')[0] for k in fresh['done']);audit={k:v for k,v in val['done'].items() if k.startswith('audit:')};negative={k:v for k,v in val['done'].items() if k.startswith('negative:')}
manifest=json.loads((r/'inputs-before.json').read_text());after={p:h(r.parent/p) for p in manifest};assert after==manifest;(r/'inputs-after.json').write_text(json.dumps(after,indent=2)+'\n')
assert (r/'fresh-final/source-manifest.json').read_bytes()==(r/'source-manifest.json').read_bytes()
resources=[]
for folder in [r/'logs',r/'fresh-extracted/logs',r/'fresh-final/logs']:
 for p in folder.glob('*.log.json'):
  rec=json.loads(p.read_text());resources.append(rec)
res={'peak_sampled_private_bytes':max(x['peak_private_bytes'] for x in resources),'max_wall_seconds':max(x['wall_seconds'] for x in resources),'cap_terminations':sum(bool(x['cap_reason']) for x in resources)}
orphans=[str(p.relative_to(r)) for p in (r/'logs').glob('*.log') if not Path(str(p)+'.json').exists()]
record={'status':'ENDPOINT_COMPILED_FINAL_FRESH_REPLAY_INCOMPLETE','accepted':False,'credit':0,'campaign_count_baseline':'21/40 beyond 39; no count changes by this lane','endpoint':'Nut8.no_cubic_8circulant_nut : Nut8.Target','exact_statement':'∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj], ¬ (Nut8.Cubic G ∧ Nut8.Nut G ∧ Nut8.Circulant 8 G)','endpoint_build_receipt':build['done']['build:Nut8Final']['receipt'],'per_support_build_receipt':build['done']['build:PerSupport']['receipt'],'endpoint_axioms':['propext','Classical.choice','Quot.sound'],'development_endpoint_leanchecker':val['done'].get('checker:Nut8Final'),'unified_modules':len(mods),'proof_closure_modules':len(closure),'certificate_count_unchanged':9172,'declaration_count':val.get('audit_declarations'),'development_full_audit':{'shards_passed':len(audit),'shards_total':128,'declarations':sum(x['declarations'] for x in audit.values()),'log':'audit.log','index':'audit-log-index.json'},'development_negative_controls':{'passed':len(negative),'total':18,'existing_olean_refusal':'negative:ExistingOlean' in negative},'final_fresh_replay':{'directory':'fresh-final','status':fresh['status'],'strict_passed':counts['build'],'strict_total':len(mods),'leanchecker_passed':counts['checker'],'leanchecker_total':len(mods),'audit_passed':counts['audit'],'audit_total':128,'negative_controls_passed':counts['negative'],'negative_controls_total':18,'next_module':next((m for m in mods if 'build:'+m not in fresh['done']),None)},'historical_initial_replay':{'strict_passes':len(initial['done']),'stopped_at':'FiniteSupport162','is_final_validation':False},'source_fixes':fixes,'packet_sha256':h(r/'nut-r7q-source.zip'),'input_files_hash_bound':len(manifest),'input_hashes_unchanged':True,'resource_receipts':res,'interrupted_attempt_logs_without_receipts':orphans,'root_acceptance':'PENDING'}
(r/'results.json').write_text(json.dumps({'365943':record},indent=2)+'\n');(r/'audit-log-index.json').write_text(json.dumps({'mode':'DEVELOPMENT_ONLY','shards':audit,'declaration_count':record['development_full_audit']['declarations']},indent=2)+'\n');(r/'negative-controls-receipts.json').write_text(json.dumps({'mode':'DEVELOPMENT_ONLY','controls':negative},indent=2)+'\n')
with (r/'audit.log').open('wb') as out:
 for key,v in audit.items():
  log=(r/v['receipt']).with_suffix('');out.write(('\nSHARD '+key+' RECEIPT '+v['receipt']+'\n').encode())
  with log.open('rb') as src:shutil.copyfileobj(src,out)
fr=record['final_fresh_replay'];count=record['development_full_audit']['declarations']
(r/'SUMMARY.md').write_text(f'''# Nut8 assembly status

The unconditional theorem `Nut8.no_cubic_8circulant_nut : Nut8.Target` compiled strictly as `nut8_target per_support`. Its printed axioms are exactly propext, Classical.choice and Quot.sound. PerSupport and all 194 support bundles compiled. All 287 regenerated certificate modules compiled; the certificate count remains 9,172.

Development validation: leanchecker passed for Nut8Final; the complete 1,024-module proof closure audit passed {len(audit)}/128 shards and inspected {count} local declarations, including generated declarations, full types, opaque-accessible bodies, flags and transitive axioms. All {len(negative)}/18 negative controls passed, including existing-olean refusal. No audit module occurs in the proof closure.

Six observed compilation fixes are recorded with before/after hashes and failure/passing receipts: FiniteSupport162–166 only raise maxRecDepth from 4096 to 8192; PerSupport replaces an unused singleton simplification with explicit empty-list membership and or_false. Other inherited sources, all r6p modules and NutInterface are byte-identical. Input hashes match before and after.

Final acceptance validation remains incomplete. The corrected source-only packet was extracted into the new empty fresh-final directory; {fr['strict_passed']}/1,151 strict rebuilds passed there. Final all-module leanchecker, audit and negative-control phases remain pending. The earlier extracted replay is historical evidence and is not final validation of the corrected packet. See GAPS.md for the precise next step. No acceptance or count credit is asserted. No background jobs remain.
''')
(r/'GAPS.md').write_text(f'''# Exact remaining work

The assembled endpoint and full closure are checked in development mode. Final fresh replay is incomplete: {fr['strict_passed']}/1,151 strict rebuilds, {fr['leanchecker_passed']}/1,151 leanchecker processes, {fr['audit_passed']}/128 audit shards and {fr['negative_controls_passed']}/18 negative controls completed in fresh-final. The next strict module is `{fr['next_module']}`. Development declaration count: {count}; final-replay declaration count remains pending.

From fresh-final, set LEAN_BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean and LEAN_PACKAGES=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages. Continue `python3 -I replay.py --resume --steps 1` (or a bounded sequential batch). The state records every passed step and validates output hashes. Do not inject development oleans. Complete every phase until replay-state.json says PASS.

Root must independently review the six authorized source fixes, exact statement correspondence and all final receipts, then decide acceptance. This lane does not self-accept or change campaign counts. Interrupted redundant PerSupport retry logs are listed in results.json; those logs are not successful validation evidence.
''')
(r/'replay-receipts.json').write_text(json.dumps({'development_build':'development-state.json','development_validation':'development-validation.json','historical_initial_replay':'fresh-extracted/replay-state.json','final_replay':'fresh-final/replay-state.json','final_counts':fr,'resource_summary':res},indent=2)+'\n')
active=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit() or int(p.name)==os.getpid():continue
 try:
  cwd=(p/'cwd').resolve();cmd=(p/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace')
  if (cwd==r or r in cwd.parents) and any(x in cmd for x in ['/bin/lean','scripts/capped.py','scripts/validate-development.py','scripts/continue-development.py','python3 -I replay.py']):active.append({'pid':int(p.name),'command':cmd})
 except OSError:pass
assert not active,active
(r/'process-snapshot.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'active_heavy_processes':active},indent=2)+'\n');print(json.dumps(record['final_fresh_replay']));print('development audited declarations',count)
