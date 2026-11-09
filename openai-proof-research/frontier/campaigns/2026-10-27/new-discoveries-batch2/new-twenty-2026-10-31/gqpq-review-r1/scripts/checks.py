from pathlib import Path
import subprocess,sys
D=Path(__file__).resolve().parents[1];b='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/'
def run(name,args,expected=0):
 r=subprocess.run(['systemd-run','--user','--scope','-p','MemoryMax=6G',sys.executable,str(D/'scripts/run.py'),name,*args]);assert r.returncode==expected,name
# Kernel checks already completed; see receipts.
run('review-audit',[b+'lean','-j1','-DwarningAsError=true','ReviewAudit.lean'])
(D/'proof/FalseControl.lean').write_text('import Endpoint\nexample : False := by exact True.intro\n')
(D/'proof/EndpointControl.lean').write_text('import Endpoint\nexample : Cover377831.SourceConjecture := Cover377831.source_refutation\n')
for n in ['FalseControl','EndpointControl']:run(n,[b+'lean','-j1','-DwarningAsError=true',n+'.lean'],1)
