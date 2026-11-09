import resource,signal,json,re,hashlib,datetime,collections
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(230)
D=Path('.');E=D/'extracted';R=D/'fresh-replay';receipt=json.loads((R/'REPLAY-RECEIPT.json').read_text());assert receipt['status']=='PASS'
log=(R/'extracted/logs/FinalAudit.log').read_text();blocks=re.findall(r'AUDIT (\S+) (\S+)\nTYPE (.*?)\nAXIOMS (.*?)\nFLAGS ([^\n]+)',log,re.S);actual=[dict(origin=o,name=n,type=t,axioms=a,flags=f) for o,n,t,a,f in blocks]
assert len(actual)==len({v['name'] for v in actual})==5924
old=json.loads((E/'inherited/declaration-inventory.json').read_text());new=json.loads((R/'declaration-inventory.json').read_text());assert actual==new;assert {x['name']:x for x in actual}=={x['name']:x for x in old}
mods=json.loads((E/'consumed-modules.json').read_text());assert len(mods)==len(set(mods))==2022
closure=set()
def visit(m):
 if m in closure:return
 closure.add(m)
 for im in re.findall(r'^import (\S+)',(E/'formal'/(m+'.lean')).read_text(),re.M):
  if (E/'formal'/(im+'.lean')).exists():visit(im)
visit('AllCases');assert closure==set(mods)
for v in actual:
 assert v['origin'] in closure and v['type']
 assert set(re.findall(r'[A-Za-z][A-Za-z.]*',v['axioms']))<={'propext','Classical.choice','Quot.sound'}
 assert v['flags']==('unsafe=false partial=true axiom=false' if v['name']=='Polyomino57.attachCheck._unsafe_rec' else 'unsafe=false partial=false axiom=false')
end={}
for n,t in [('finiteCases','Polyomino57.Diagonal.FiniteCases'),('universalContainer','Polyomino57.UniversalContainer 11 Polyomino57.witness'),('eligible','Polyomino57.EligibleSize 11 57'),('minimum_le','LE.le.{0} (Polyomino57.minimumSize 11) 57'),('source_refutation','¬Polyomino57.SourceFormula')]:
 v=next(x for x in actual if x['name']=='Polyomino57.Diagonal.FiniteProof.AllCases.'+n);assert v['type']==t;(end.update({n:v}))
manifest=json.loads((E/'source-manifest.json').read_text());assert len(manifest)==2023
for p,v in manifest.items():
 for base in [E,R/'extracted']:assert hashlib.sha256((base/p).read_bytes()).hexdigest()==v['sha256']
for m in mods:assert not (R/'extracted/logs'/(m+'.log')).read_bytes()
runs=[json.loads(x) for x in (R/'extracted/runs.jsonl').read_text().splitlines()];assert runs==receipt['build_reports'];assert len(runs)==2024
assert all(x['rc']==0 and x['kill_reason']==None and x['seconds']<230 and x['peak_group_rss']<2800*1024**2 and x['interval_seconds']==.045 for x in runs)
result=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),actual_records=5924,complete_fresh_records_equal_frozen=True,exact_consumed_closure=2022,source_hashes=2023,records_sha256=hashlib.sha256((R/'declaration-inventory.json').read_bytes()).hexdigest(),audit_log_sha256=hashlib.sha256((R/'extracted/logs/FinalAudit.log').read_bytes()).hexdigest(),receipt_sha256=hashlib.sha256((R/'REPLAY-RECEIPT.json').read_bytes()).hexdigest(),max_sampled_group_rss_bytes=max(x['peak_group_rss'] for x in runs),max_stage_seconds=max(x['seconds'] for x in runs),summed_stage_seconds=sum(x['seconds'] for x in runs),endpoint_records=end,origins=dict(collections.Counter(x['origin'] for x in actual)),qualification='45ms sampled group RSS; unsampled transients not ruled out',credit=0,root_acceptance=False)
Path('fresh-audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['origins','endpoint_records']},indent=2))
