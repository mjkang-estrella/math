from pathlib import Path
import subprocess,json,re,hashlib,collections
base=Path('openai-proof-research');out=Path(__file__).parent
files=subprocess.check_output(['git','ls-files','-co','--exclude-standard',str(base)],text=True).splitlines();ex={369163}; used=[]
for s in files:
 p=Path(s)
 if any(x in p.parts for x in ['frozen','raw','corpus','snapshots','sources','.lake']) or out in p.parents:continue
 if p.suffix not in ['.md','.json','.jsonl','.txt']:continue
 if not any(w in p.name.lower() for w in ['reservation','ledger','coverage','result','review','reject','next','accepted','queue','decision','status','report','notes','records','pool','screen']):continue
 if p.stat().st_size>10000000:continue
 t=p.read_text(errors='replace');ex.update(map(int,re.findall(r'(?<!\d)[2-4]\d{5}(?!\d)',t)));used.append(s)
rows=[];tot=collections.Counter()
KW=['polynomial','prime','integer','divisor','congruen','group','ring','field','modular','matrix','eigen','algebra','permutation','partition','binomial','coefficient','sum','sequence','diophant','galois','ideal','determinant','lattice','quadratic','character','residue']
for p in sorted((base/'frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 for line in p.open():
  d=json.loads(line);i=d['mathdb_id'];st=d.get('statement') or ''
  tot['all']+=1
  if i%3!=2: continue
  tot['mod2']+=1
  if i in ex: tot['ex']+=1; continue
  if not st or d.get('solution_count') or d.get('status') not in ['open','unsolved',None]:continue
  tot['cand']+=1
  txt=(d['title']+' '+st+' '+' '.join(d.get('tags') or [])).lower()
  score=sum(w in txt for w in KW)
  rows.append((score,d))
rows.sort(key=lambda x:(-x[0],len(x[1]['statement'])))
(out/'selection-pool.json').write_text(json.dumps([d for _,d in rows if _>=3],indent=1))
(out/'exclusion-index.json').write_text(json.dumps({'excluded_count':len(ex),'n_index_files':len(used),'index_files_sha256':hashlib.sha256('\n'.join(used).encode()).hexdigest(),'policy':'conservative 6-digit occurrence in review/coverage/ledger/reservation/result/queue/decision/NEXT/status/report/notes/records/pool/screen artifacts; excludes raw/corpus/source/frozen'},indent=1))
print(tot, len([1 for s,_ in rows if s>=3]))
