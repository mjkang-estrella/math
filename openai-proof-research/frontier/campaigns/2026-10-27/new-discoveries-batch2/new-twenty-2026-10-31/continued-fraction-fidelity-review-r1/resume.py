from pathlib import Path
import os,resource,subprocess,time,json,hashlib,zipfile,re,datetime,math
R=Path(__file__).resolve().parent; A=R.parent/'expanded-corpus-r45'
T=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
F=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,)*2);resource.setrlimit(resource.RLIMIT_CPU,(600,)*2);os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
E=R/'extracted'
s=(E/'Candidate.lean').read_text()
paths=[E]+[F/'.lake/packages'/p/'.lake/build/lib/lean' for p in ['mathlib','batteries','Qq','aesop','proofwidgets','LeanSearchClient','importGraph','plausible','Cli']]
env={'PATH':str(T)+':'+os.defpath,'LEAN_PATH':':'.join(map(str,paths)),'LEAN_NUM_THREADS':'1','MALLOC_ARENA_MAX':'2','MIMALLOC_PURGE_DELAY':'0'}
logs=json.loads((R/'runs.json').read_text())
def run(label,args,expected=0):
 start=time.monotonic()
 def caps(): resource.setrlimit(resource.RLIMIT_CPU,(120,)*2)
 r=subprocess.run(args,cwd=E,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=150,preexec_fn=caps)
 p=R/(label+'.log');p.write_bytes(r.stdout);logs.append({'label':label,'args':list(map(str,args)),'exit_code':r.returncode,'seconds':time.monotonic()-start,'sha256':sha(p),'expected_success':expected==0})
 (R/'runs.json').write_text(json.dumps(logs,indent=2));print(label,r.returncode,flush=True)
 assert (r.returncode==0)==(expected==0)
lean=[str(T/'lean'),'-j1','-M4096','-DwarningAsError=true']

audit=(E/'Audit.lean').read_text().replace('open Lean Elab Command','set_option pp.proofs true\nset_option pp.explicit true\nset_option pp.universes true\nset_option pp.fullNames true\nopen Lean Elab Command').replace('let axs ← collectAxioms name','logInfo m!"FULL_TYPE {name} : {ci.type}"\n        if let some v := ci.value? true then\n          logInfo m!"FULL_VALUE {name} := {v}"\n        let axs ← collectAxioms name')
(E/'ReviewAudit.lean').write_text(audit)
run('full-origin-audit',lean+['ReviewAudit.lean'])
run('module-leanchecker',[str(T/'leanchecker'),'--verbose','Candidate'])
run('print-all',lean+['PrintAll.lean'])
(E/'BadTable.lean').write_text(s.replace('![55,9,5,2','![54,9,5,2'))
run('negative-table',lean+['BadTable.lean'],1)
(E/'BadRank.lean').write_text(s.replace(')).card = 6 ∧',')).card = 7 ∧'))
run('negative-rank',lean+['BadRank.lean'],1)
(E/'SorryControl.lean').write_text('import Mathlib\ntheorem bad : False := by sorry\n')
run('negative-sorry',lean+['SorryControl.lean'],1)
(E/'AxiomControl.lean').write_text('axiom injected : False\n')
run('axiom-control-build',lean+['-o','AxiomControl.olean','AxiomControl.lean'])
(E/'RejectAxiom.lean').write_text(audit.replace('import Candidate','import AxiomControl').replace('== `Candidate','== `AxiomControl'))
run('negative-axiom-audit',lean+['RejectAxiom.lean'],1)
run('negative-checker-missing',[str(T/'leanchecker'),'ReviewMissingModule'],1)
(E/'ForgedControl.lean').write_text('import Lean\nopen Lean Elab Command\nrun_cmd do\n  let env ← getEnv\n  let decl := Declaration.thmDecl { name := `forged, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }\n  match env.addDeclCore 0 0 decl none false with\n  | .ok e => setEnv e\n  | .error _ => throwError "injection failed"\n')
run('forged-control-build',lean+['-o','ForgedControl.olean','ForgedControl.lean'])
run('negative-checker-forged',[str(T/'leanchecker'),'--verbose','ForgedControl'],1)
manifest=json.loads((F/'lake-manifest.json').read_text())
(R/'replay-receipt.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'inventory':[{'name':p.name,'size':p.stat().st_size} for p in [E/'Candidate.lean',E/'Audit.lean',E/'replay.py']],'packet_sha256':sha(A/'proof-packet.zip'),'candidate_sha256':sha(E/'Candidate.lean'),'lean_sha256':sha(T/'lean'),'leanchecker_sha256':sha(T/'leanchecker'),'manifest_sha256':sha(F/'lake-manifest.json'),'mathlib':[p for p in manifest['packages'] if p['name']=='mathlib'],'env':env,'limits':{'cpus':sorted(os.sched_getaffinity(0)),'virtual_GiB':32,'Lean_MiB':4096,'cpu_seconds_per_child':120,'wall_seconds_per_child':150,'j':1},'runs':logs,'trust':'prebuilt imported caches trusted; module checker reuses Lean kernel; no upstream source-to-olean attestation'},indent=2))
