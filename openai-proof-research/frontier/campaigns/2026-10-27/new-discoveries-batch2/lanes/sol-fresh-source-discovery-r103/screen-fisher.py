from pathlib import Path
import subprocess,json,hashlib,datetime
P=Path(__file__).resolve().parent
args=['rg','-n','-i','--hidden','--glob','*SUMMARY*','--glob','*summary*','--glob','*discovery*','--glob','*FINDINGS*','--glob','*findings*','--glob','*PROOF*','--glob','*proof*','--glob','*review*','--glob','*ledger*','--glob','!**/sol-fresh-source-discovery-r103/**',r'Eskenazis|Gavalakis|Fisher.{0,70}(mixture|minimi|Schur)|2308\.15997|2609\.11418','openai-proof-research']
r=subprocess.run(args,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
(P/'fisher-duplicate-hits.txt').write_text(r.stdout);(P/'fisher-duplicate-screen.json').write_text(json.dumps({'args':args,'exit':r.returncode,'stderr':r.stderr,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'hits_sha256':hashlib.sha256(r.stdout.encode()).hexdigest()},indent=2));print(r.returncode,r.stdout[:13000])
