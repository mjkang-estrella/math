from pathlib import Path
import os,subprocess,json
D=Path(__file__).resolve().parents[1];F=D/'extracted'; bins=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin'); deps=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
env={k:v for k,v in os.environ.items() if not k.startswith('LEAN_')};env['PATH']=str(bins)+':'+env['PATH'];env['LEAN_PATH']=str(F/'lean')+':'+':'.join(str(p) for p in sorted(deps.glob('*/.lake/build/lib/lean')))
for name,cmd in [('strict-build',[str(bins/'lean'),'-j1','-DwarningAsError=true','-o','lean/Hierarchy.olean','lean/Hierarchy.lean']),('full-audit',[str(bins/'lean'),'-j1','-DwarningAsError=true','lean/IndependentAudit.lean']),('leanchecker',[str(bins/'leanchecker'),'-j1','Hierarchy']),('sanity',[str(bins/'lean'),'-j1','-DwarningAsError=true','lean/Sanity.lean'])]:
 r=subprocess.run(['python',str(D/'scripts/limited.py'),name,*cmd],cwd=F,env=env); assert r.returncode==0
 receipt=json.loads((D/'logs'/f'{name}.receipt.json').read_text()); assert receipt['returncode']==0,receipt
