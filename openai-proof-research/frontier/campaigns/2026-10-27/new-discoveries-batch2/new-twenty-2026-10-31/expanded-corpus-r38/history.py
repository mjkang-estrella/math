from pathlib import Path
import json,subprocess,hashlib
H=Path(__file__).resolve().parent;root=H.parents[5]; d=json.loads((H/'extracted.json').read_text()); out={}
for i,e in d.items():
 title=e['record']['title']; args=['rg','-n','-F','-e',i,'-e',title,'--glob','*.md','--glob','*results*.json','--glob','*ledger*.json','--glob','!reservation.json','--glob','!**/expanded-corpus-r38/**',str(root/'frontier/campaigns')]
 p=subprocess.run(args,capture_output=True,text=True); lines=p.stdout.splitlines(); out[i]={'searched_literals':[i,title],'matches':[l[:3000] for l in lines], 'exit_code':p.returncode}
(H/'history-matches.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
for i,e in out.items():print(i,len(e['matches']));print('\n'.join(e['matches'][:3]))
ctx=[]
for p in [H.parent/'ledger.json',H.parent.parent/'ledger.json',H.parent.parent/'prior-campaign-context.json',root/'sources/upstream.json']:
 b=p.read_bytes();j=json.loads(b);ctx.append({'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'keys':list(j)})
(H/'context-receipts.json').write_text(json.dumps(ctx,indent=2)+'\n')
