from pathlib import Path
import json,hashlib,datetime,xml.etree.ElementTree as E
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
ns={'a':'http://www.w3.org/2005/Atom'}
meta=[]
for f in [L/'frozen/targeted.xml',L/'frozen/leake.xml']:
 for e in E.parse(f).findall('a:entry',ns):
  meta.append({k:e.find('a:'+k,ns).text for k in ['id','title','published','updated']})
(L/'chronology.json').write_text(json.dumps(meta,indent=2))
ledger=json.loads((L/'admin/ledger.json').read_text());prior=json.loads((L/'admin/prior-campaign-context.json').read_text())
(L/'administrative-read.json').write_text(json.dumps({'ledger_counts':{k:ledger[k] for k in ['accepted_count','total_accepted_count','next_global_outcome_number']},'accepted_titles':[r['title'] for r in ledger['accepted']],'prior_top_level_keys':list(prior),'prior_snapshot_bytes':(L/'admin/prior-campaign-context.json').stat().st_size,'policy':'administrative snapshot only; not compared with changing originals'},indent=2))
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
(L/'provenance.json').write_text(json.dumps({'lane':str(L),'date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'role':'solo research sub-agent','target':'Leake-Ryder1811.06382v1 Conjecture2.5','status':'unresolved','credit':0,'counts':[9,39,40],'guard':{'path':str(guard),'sha256':sha(guard),'AS_bytes':536870912,'groupRSS_bytes':536870912,'CPU_seconds':210,'wall_seconds':230,'environment':{'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},'cap_raises':False},'replay_command':'OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python '+str(guard)+' python '+str(L/'replay.py'),'replay_guard_observed':{'exit':0,'sampled_peak_group_rss':84742144,'wall_seconds':46.40529055602383},'scientific_bindings':'source-bindings.json and access.jsonl','chronology':'chronology.json','history':'frozen r266 history-hits/provenance; no recursive duplication; no active r271/r272 outputs read','access_limitations':'current registry HEAD unknown; inherited denied routes parked; bounded selected primary-body comparison only','external_mutations':False,'children':False,'lean_or_manuscript':False,'eight_additional_families_screened':False},indent=2))
rows=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ['final-manifest.json','verification-receipt.json']:
  rows.append({'path':str(p.relative_to(L)),'bytes':p.stat().st_size,'sha256':sha(p)})
(L/'final-manifest.json').write_text(json.dumps({'excludes':['final-manifest.json','verification-receipt.json'],'files':rows},indent=2));print('manifest files',len(rows))
