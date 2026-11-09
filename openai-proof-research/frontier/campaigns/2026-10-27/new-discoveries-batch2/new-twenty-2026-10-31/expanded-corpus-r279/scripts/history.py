import datetime, hashlib, json, resource, subprocess
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent.parent
records=json.loads((p/'extracted-records.json').read_text())
cmd=['rg','-n','-F','--glob','*.md','--glob','*.txt','--glob','*.json','--glob','!reservation.json','--glob','!launch.json','--glob','!TASK.txt','--glob','!history*']
terms={}
for i,v in records.items():
 r=v['record']; terms[i]=[r['title'],r['source_url']]
 for q in terms[i]:cmd+=['-e',q]
cmd+=['openai-proof-research']
r=subprocess.run(cmd,capture_output=True,text=True,timeout=100)
assert r.returncode in (0,1)
lines=[s for s in r.stdout.splitlines() if '/expanded-corpus-r279/' not in s]
(p/'history-title-source-matches.txt').write_text('\n'.join(lines)+'\n')
(p/'history-title-source-check.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'terms':terms,'scope':'project markdown/text/json; exact literal titles and primary URLs; prior ID/arXiv/family screen separately retained','matches':len(lines),'sha256':hashlib.sha256(('\n'.join(lines)+'\n').encode()).hexdigest(),'limits':'Full inherited corpus/catalogue hits are routing, not past mathematical review. ID numeric matches include unrelated counts. No assignment-index novelty inference.'},indent=2)+'\n')
print(json.dumps({'matches':len(lines),'first_paths':list(dict.fromkeys(x.split(':')[0] for x in lines))[:15]}))
