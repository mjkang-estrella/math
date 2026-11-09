import pathlib,json,subprocess,hashlib,re,resource,os
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(90,90));os.sched_setaffinity(0,{0,1})
L=pathlib.Path(__file__).resolve().parent; root=L.parents[5]; data=json.load(open(L/'extracted.json')); out={}
for i,v in data.items():
 r=v['record']; a=re.search(r'\d{4}\.\d{4,5}',r['source_url'] or ''); pats=[rf'\b{i}\b',re.escape(r['title'])]+([re.escape(a[0])] if a else [])
 p=subprocess.run(['rg','-n','-i','--max-count','4','|'.join(pats),str(root),'--glob','*.md','--glob','*ledger*.json','--glob','*results.json','--glob','!**/expanded-corpus-r35/**','--glob','!**/copies/**','--glob','!**/frozen*/**','--glob','!**/originals/**','--glob','!**/outside/**','--glob','!**/history-flat/**'],capture_output=True,text=True,timeout=15)
 out[i]={'patterns':pats,'exit_code':p.returncode,'hits':p.stdout.splitlines(),'stderr':p.stderr}
(L/'history-matches.json').write_text(json.dumps(out,indent=2)+'\n')
for i,v in out.items():
 print(i,len(v['hits']));print('\n'.join(x[:450] for x in v['hits'][:3]))
