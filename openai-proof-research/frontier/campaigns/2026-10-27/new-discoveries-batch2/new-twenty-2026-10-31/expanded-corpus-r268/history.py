from pathlib import Path
import subprocess,json,resource,time
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent;root=next(x for x in p.parents if x.name=='openai-proof-research'); d=json.loads((p/'extracted.json').read_text());out={}
for i,x in d.items():
 r=x['record'];terms=[i,r['title'],r['source_url'].split('/abs/')[-1]]
 a=subprocess.run(['rg','-l','-F',*sum((['-e',t] for t in terms),[]),str(root/'frontier/campaigns/2026-10-27'),'--glob','*.json','--glob','*.md','--glob','*.txt','--glob','!mathdb-normalized-chunk-*','--glob','!screening-tags.jsonl','--glob','!routing-queue.jsonl'],capture_output=True,text=True,timeout=8)
 paths=[s for s in a.stdout.splitlines() if str(p) not in s];out[i]={'terms':terms,'paths':paths,'scope':'project text/json/jsonl, excluding normalized corpus and large metadata routing files; numeric hits may be unrelated','returncode':a.returncode};print(i,len(paths),[s.split('new-twenty-2026-10-31/')[-1] for s in paths if 'results.json' in s][:10])
(p/'historical-search.json').write_text(json.dumps(out,indent=2)+'\n');print('completed CPU',time.process_time())
