from pathlib import Path
import json,re,subprocess
H=Path(__file__).resolve().parent; root=H.parents[5];out={}
for i,e in json.loads((H/'extracted.json').read_text()).items():
 r=e['record']; aliases=re.findall(r'\d{4}\.\d{4,5}',r['source_url'] or '')
 aliases+=re.findall('“([^”]+)”',r['source_name'] or '')
 args=['rg','-n','-i','-F']
 for a in aliases:args+=['-e',a]
 args+=['--glob','*.md','--glob','*results*.json','--glob','*ledger*.json','--glob','!**/expanded-corpus-r38/**',str(root/'frontier/campaigns')]
 p=subprocess.run(args,capture_output=True,text=True);out[i]={'aliases':aliases,'matches':[s[:3500] for s in p.stdout.splitlines()],'exit_code':p.returncode}
(H/'alias-matches.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
for i,e in out.items():
 print(i,e['aliases'],len(e['matches']))
 for s in e['matches'][:4]:print(s)
