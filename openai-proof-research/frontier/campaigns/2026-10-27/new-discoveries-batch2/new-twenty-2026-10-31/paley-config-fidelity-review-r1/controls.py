from run import *
(L/'FalseWitness.lean').write_text('import V3Config355701\nexample : MathDB355701.S4.card = 5 := by decide +kernel\n')
(L/'FalseYip.lean').write_text('import Yip355956\nexample : IsGreatest (MathDB355956.admissibleR 5 8 3) 2 := by decide +kernel\n')
(L/'BadAudit.olean').write_bytes(b'This is deliberately not an olean.\n')
out=[]
for n in ['FalseWitness','FalseYip']:out.append(run('negative-'+n,[str(B/'lean'),'-j1','-DwarningAsError=true',n+'.lean']))
for n in ['BadAudit','AbsentReviewModule']:out.append(run('negative-'+n,[str(B/'leanchecker'),n]))
(D/'controls.json').write_text(json.dumps(out,indent=2))
# Pin binary and mathlib commit without git operations.
mr=P/'mathlib';gp=mr/'.git'; g=pathlib.Path(gp.read_text().strip().removeprefix('gitdir: ')) if gp.is_file() else gp
if not g.is_absolute():g=mr/g
head=(g/'HEAD').read_text().strip();rev=head
if head.startswith('ref: '):
 ref=head[5:];rp=g/ref
 if rp.exists():rev=rp.read_text().strip()
 else:rev=next(s.split()[0] for s in (g/'packed-refs').read_text().splitlines() if s.endswith(' '+ref))
rec={'lean_path':str(B/'lean'),'lean_sha256':hashlib.sha256((B/'lean').read_bytes()).hexdigest(),'mathlib_head':head,'mathlib_commit':rev,'caps':{'AS_GiB_initial':12,'AS_GiB_adjusted':64,'RSS_GiB_systemd_MemoryMax':6,'CPU_seconds':120,'wall_seconds':140,'CPUQuota':'200%','affinity':sorted(os.sched_getaffinity(0))[:2],'threads':1,'MALLOC_ARENA_MAX':'2'},'version':subprocess.check_output([str(B/'lean'),'--version'],text=True)}
(D/'environment.json').write_text(json.dumps(rec,indent=2));print(rec)
