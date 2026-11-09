from pathlib import Path
import json,re,hashlib,sys
r=Path(__file__).resolve().parent
if sys.argv[1]=='audit':
 mods=(r/'packet/module-order.txt').read_text().splitlines()
 old=(r/'packet/src/Audit.lean').read_text();start=old.index('  let localModules : Array String := #[');end=old.index('\n',start)
 text='import ReplayEndpoint\nimport Pilot500\n'+old
 text=text[:text.index('  let localModules : Array String := #[')]+text[text.index('  let localModules : Array String := #['):]
 text=re.sub(r'  let localModules : Array String := #\[[^\n]*', '  let localModules : Array String := #['+','.join(json.dumps(x) for x in mods)+']',text)
 text=text.replace('| none => "Audit"','| none => "AuditR3"')
 (r/'packet/src/AuditR3.lean').write_text(text)
elif sys.argv[1]=='report':
 res=json.loads((r/'results.json').read_text());mods=(r/'packet/module-order.txt').read_text().splitlines();res['status']='conditional; no acceptance claimed';res['module_count']=len(mods)
 res['endpoint']={'name':'Percolation.Replay.not_conjecture20_after2000','statement':'ReplayFrontierUnsat5 → ¬ Conjecture20','remaining_prop':'¬ ∃ v : SatVar → Bool, (∀ c ∈ inputCNF5, CNF.Holds v c) ∧ (∀ c ∈ Replay.prefix2000, CNF.Holds (v ∘ decodeVar) c)','unconditional':False}
 res['prefix']=json.loads((r/'pilot-info.json').read_text());res['prefix']['proved_distinct_additions']=2000;res['prefix']['remaining_additions']=res['prefix']['total_additions']-2000
 fresh=r/'fresh-extracted';rows=[]
 for m in mods:
  row={'module':m}
  for phase in ['build','check']:
   p=fresh/'logs'/f'{phase}-{m}.receipt.json';a=json.loads(p.read_text());log=(fresh/'logs'/f'{phase}-{m}.log').read_text();match=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log)
   secs=0
   for part in match[1].split(':'):secs=secs*60+float(part)
   a['wall_seconds']=secs;row[phase]=a
   assert a['exit']==0,(m,phase)
  rows.append(row)
 (r/'module-times.json').write_text(json.dumps(rows,indent=2))
 res['fresh_replay']={'compiled':len(rows),'checked':len(rows),'build_wall_seconds':sum(x['build']['wall_seconds'] for x in rows),'check_wall_seconds':sum(x['check']['wall_seconds'] for x in rows),'longest_wall_seconds':max(x[p]['wall_seconds'] for x in rows for p in ['build','check']),'peak_group_rss_kib':max(x[p]['peak_group_rss_kib'] for x in rows for p in ['build','check'])}
 findings=[]
 for m in mods:
  t=(fresh/'src'/(m+'.lean')).read_text();t=re.sub(r'/\-.*?\-/','',t,flags=re.S);t=re.sub(r'--[^\n]*','',t);t=re.sub(r'"(?:[^"\\]|\\.)*"','""',t)
  for pat in [r'\b(sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool|bv_decide|implemented_by|extern)\b',r'_unsafe_rec']:
   if re.search(pat,t):findings.append([m,pat])
 assert not findings,findings
 res['source_scan']={'files':len(mods),'findings':findings};res['source_zip_sha256']=hashlib.sha256((r/'source-only.zip').read_bytes()).hexdigest()
 log=(fresh/'logs/build-ReplayEndpoint.log').read_text();res['endpoint_axiom_print']=next(x for x in log.splitlines() if 'depends on axioms' in x)
 assert 'sorryAx' not in log
 res['metadata_audit']=next(x for x in (fresh/'logs/build-AuditR3.log').read_text().splitlines() if 'metadata audit passed' in x)
 (r/'results.json').write_text(json.dumps(res,indent=2));print(json.dumps(res['fresh_replay'],indent=2))
