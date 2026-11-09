import pathlib,json,hashlib,subprocess,re,datetime
L=pathlib.Path(__file__).resolve().parent
p=next((L/'science').glob('*2610.17046.pdf'));q=L/'source-reextracted.txt'
r=subprocess.run(['pdftotext','-layout',str(p),str(q)],capture_output=True,text=True,timeout=35)
(L/'extraction.json').write_text(json.dumps({'exit':r.returncode,'stderr':r.stderr,'sha256':hashlib.sha256(q.read_bytes()).hexdigest(),'matches_frozen_text':q.read_bytes()==next((L/'science').glob('*2610.17046.txt')).read_bytes()},indent=2))
txt=(L/'live/companion-abs.html').read_text();txt=re.sub(r'\s+',' ',re.sub('<[^>]+>',' ',txt));i=txt.find('Submission history');print(txt[i:i+600])
rows=json.loads((L/'bindings.json').read_text()); rows.append({'original':'/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py','sha256':hashlib.sha256(pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py').read_bytes()).hexdigest(),'role':'guard immutable reference; no duplicate'})
(L/'bindings.json').write_text(json.dumps(rows,indent=2))
print((L/'extraction.json').read_text())
