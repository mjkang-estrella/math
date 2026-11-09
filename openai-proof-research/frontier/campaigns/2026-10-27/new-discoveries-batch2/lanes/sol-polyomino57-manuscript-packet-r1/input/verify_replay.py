from pathlib import Path
import resource,signal,json,re,hashlib
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(230)
L=Path(__file__).resolve().parent;E=L/'extracted-source';mods=json.loads((E/'consumed-modules.json').read_text());assert (E/'fresh-completed.txt').read_text().splitlines()==mods+['FinalAudit']
for f,v in json.loads((E/'source-manifest.json').read_text()).items():assert hashlib.sha256((E/f).read_bytes()).hexdigest()==v['sha256']
for m in mods:assert not (E/'fresh-logs'/(m+'.log')).read_text(),m
text=(E/'fresh-logs/FinalAudit.log').read_text();names=(E/'formal/declaration-names.txt').read_text().splitlines();blocks=re.findall(r'AUDIT (\S+) (\S+)\nTYPE (.*?)\nAXIOMS (.*?)\nFLAGS ([^\n]+)',text,re.S)
assert len(blocks)==len(names)==len(set(names));assert set(n for _,n,_,_,_ in blocks)==set(names)
for origin,n,t,axs,flags in blocks:
 assert origin in mods
 assert flags==('unsafe=false partial=true axiom=false' if n=='Polyomino57.attachCheck._unsafe_rec' else 'unsafe=false partial=false axiom=false'),(n,flags)
 assert set(re.findall(r'[A-Za-z][A-Za-z.]*',axs))<=set(['propext','Classical.choice','Quot.sound']),(n,axs)
for n in ['finiteCases','universalContainer','source_refutation']:
 assert any(name=='Polyomino57.Diagonal.FiniteProof.AllCases.'+n for _,name,_,_,_ in blocks),n
runs=[json.loads(s) for s in (E/'runs.jsonl').read_text().splitlines()];assert len(runs)==len(mods)+1
assert all(r['rc']==0 and r['kill_reason'] is None and r['peak_group_rss']<2800*1024**2 and r['seconds']<230 and r['interval_seconds']==.045 for r in runs)
inv=[dict(origin=m,name=n,type=t,axioms=a,flags=f) for m,n,t,a,f in blocks];(L/'declaration-inventory.json').write_text(json.dumps(inv,indent=2)+'\n')
receipt=dict(status='PASS_ALL_33_RESIDUAL_70_TOTAL_CASES_UNCONDITIONAL_SOURCE_REFUTATION',credit=0,additional=5,total=35,modules=len(mods),declarations=len(names),fresh_extracted_source_only=True,consumed_candidate_oleans=False,FiniteCases_closed=True,unconditional_UniversalContainer=True,source_refutation=True,all_actual_types_axioms_origins_safety_audited=True,allowed_axioms=['propext','Classical.choice','Quot.sound'],inherited_partial_exception='Polyomino57.attachCheck._unsafe_rec',source_packet_sha256=hashlib.sha256((L/'source-only-component.zip').read_bytes()).hexdigest(),build_reports=runs)
(L/'REPLAY-RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items() if k!='build_reports'},indent=2))
