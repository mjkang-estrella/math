from pathlib import Path
import json,subprocess,datetime
P=Path(__file__).resolve().parent;root=Path('openai-proof-research');rows=json.loads((P/'duplicate-corpus.json').read_text());pat=r'Eskenazis|Gavalakis|Fisher.{0,70}(mixture|minimi|Schur)|2308\.15997|2609\.11418';hits=[];fail=[]
for i in range(0,len(rows),150):
 fs=[str(root/x[0]) for x in rows[i:i+150]];r=subprocess.run(['rg','-l','-i',pat,'--',*fs],text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 if r.returncode not in [0,1]:fail.append([i,r.returncode,r.stderr])
 hits.extend(r.stdout.splitlines())
(P/'fisher-full-screen.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'pattern':pat,'corpus_files':len(rows),'corpus_manifest':'duplicate-corpus.json','hits':hits,'failures':fail,'interpretation':'Actual Q3 not found in prior reports; r94 references GM entropy mechanism only; snapshots/path inventories and unrelated Eskenazis results are not source resolutions.'},indent=2));print(len(rows),len(hits),len(fail))
