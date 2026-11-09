import pathlib,json,re,subprocess,resource,os
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
p=pathlib.Path(__file__).resolve().parent;r=json.loads((p/'reservation.json').read_text())
pat='|'.join(re.escape(x['title']) for x in r['rows'])
args=['rg','-n','-F','--glob','*.md','--glob','*.json','--glob','*.txt','--glob','!**/expanded-corpus-r55/**','--glob','!**/expanded-corpus-r54/**','--glob','!**/sources/**','--glob','!**/raw/**','--glob','!**/frozen/**','--glob','!reservation.json','--glob','!*tree*','--glob','!*index*','--glob','!*queue*','--glob','!*pool*','--glob','!*history*','--glob','!*ranked*','--glob','!*receipt*']
for x in r['rows']:args+=['-e',x['title']]
a=subprocess.run(args+[str(p.parent.parent.parent)],capture_output=True,text=True,timeout=60)
(p/'history-titles.txt').write_text(a.stdout);print('status',a.returncode,'bytes',len(a.stdout));print(a.stdout[:6000])
