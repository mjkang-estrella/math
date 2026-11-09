from pathlib import Path
import subprocess,json
O=Path(__file__).resolve().parent;r=json.loads((O/'records.json').read_text());pats=[]
for i,x in r.items():pats+=['-e',i,'-e',x['title']]
cmd=['rg','-n','-F','--max-count','4','--max-columns','1600',*pats,'--glob','*disposition*.json','--glob','*review*.json','--glob','*reject*.json','--glob','*results.json','--glob','*.md','--glob','!**/sources/**','--glob','!**/raw/**','--glob','!**/deps/**','--glob','!**/expanded-corpus-r58/**','/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns']
p=subprocess.run(cmd,capture_output=True,text=True,timeout=85);(O/'history-focused.log').write_text(p.stdout);(O/'history-focused-command.json').write_text(json.dumps({'cmd':cmd,'exit':p.returncode,'stderr':p.stderr,'limits':'Maximum four lines per file, 1600 columns; numeric coincidences and prior metadata must be distinguished from technical review. Broader read-and-hash attempt hit CPU cap; no claim it completed.'},indent=2)+'\n'); print(p.stdout[:12000]);print('OUTPUT_BYTES',len(p.stdout))
