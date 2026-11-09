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


(R/'negative-sorry-startup-failure.log').write_bytes((R/'negative-sorry.log').read_bytes())
(E/'SorryControl.lean').write_text('import Lean\ntheorem bad : False := by sorry\n')
run('negative-sorry',lean+['SorryControl.lean'],1)
p=E/'ReviewAudit.lean';p.write_text(p.read_text().replace('set_option pp.proofs true','set_option maxRecDepth 10000\nset_option maxHeartbeats 8000000\nset_option pp.maxSteps 1000000\nset_option pp.proofs true'))
run('full-origin-audit-unabridged',lean+['ReviewAudit.lean'])
p=E/'RejectAxiom.lean';p.write_text('\n'.join(l for l in p.read_text().splitlines() if not l.startswith('#print'))+'\n')
run('negative-axiom-audit',lean+['RejectAxiom.lean'],1)
rec=json.loads((R/'replay-receipt.json').read_text());rec['runs']=logs;(R/'replay-receipt.json').write_text(json.dumps(rec,indent=2))
