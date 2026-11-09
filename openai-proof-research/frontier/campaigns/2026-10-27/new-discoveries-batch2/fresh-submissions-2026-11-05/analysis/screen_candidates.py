from pathlib import Path
import subprocess,json,re,hashlib
base=Path('openai-proof-research');out=Path(__file__).parent
files=subprocess.check_output(['rg','--files',str(base)],text=True).splitlines();ex={369163}; used=[]
for s in files:
 p=Path(s)
 if any(x in p.parts for x in ['frozen','raw','corpus','snapshots','sources','.lake']) or out in p.parents:continue
 if p.suffix not in ['.md','.json','.jsonl','.txt']:continue
 if not any(w in p.name.lower() for w in ['reservation','ledger','coverage','result','review','reject','next','accepted','queue','decision']):continue
 if p.stat().st_size>10000000:continue
 t=p.read_text(errors='replace');ex.update(map(int,re.findall(r'(?<!\d)[3-4]\d{5}(?!\d)',t)));used.append(s)
rows=[]
for p in sorted((base/'frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 for line in p.open():
  d=json.loads(line);i=d['mathdb_id'];st=d.get('statement') or ''
  if i%3!=1 or i in ex or not st or d.get('solution_count') or d.get('status') not in ['open','unsolved',None]:continue
  score=sum(w in (d['title']+' '+st).lower() for w in ['inequal','convex','concav','monoton','integral','gamma','polynomial','positive','bound','sequence'])
  if score>=2:rows.append((score,d))
rows.sort(key=lambda x:(-x[0],len(x[1]['statement'])))
(out/'selection-pool.json').write_text(json.dumps([d for _,d in rows],indent=2));(out/'exclusion-index.json').write_text(json.dumps({'excluded_count':len(ex),'index_files':used,'policy':'conservative six-digit occurrence in review/coverage/ledger/reservation/result/queue/decision/NEXT artifacts; excludes raw/corpus/source/frozen snapshots'},indent=2))
for score,d in rows[:60]:print(d['mathdb_id'],score,d['title'],d['statement'][:1000].replace('\n',' '))
